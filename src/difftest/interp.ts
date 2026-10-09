/**
 * Interpreter for kernel terms with proofs erased (specification 6.8, milestone 9).
 *
 * The input is `K.erase(term)`: `Sort`, `Pi`, `Sigma` and `Farkas` are gone, and `Lam`/`Let`
 * still bind exactly one variable, so de Bruijn indices are unchanged.  Everything here is
 * the *untrusted* side of the trust boundary: this module exists to disagree with the
 * verified function, and a disagreement is what the differential test looks for.
 *
 * The interpretation rules:
 *
 *   - `fixWf` becomes **real recursion**: the induction hypothesis is a first-class value
 *     that, once applied to a new state and its two measure proofs, calls `fixWf` again.
 *   - vectors (`Vec A n`) are JS arrays, `Sigma` is `{ tag: "pair", first, second }`,
 *     `Sum` is `{ tag: "inl" | "inr", value }`, `Int` is a `bigint` (exact for the whole
 *     safe-integer range and beyond, so an overflow shows up as a mismatch rather than as a
 *     rounded coincidence).
 *   - `add`/`sub`/`neg`/`mulConst`/`divFloor`/`divTrunc` run on bigints, `ifLe` compares and
 *     applies the chosen branch, `len`/`get`/`append`/`slice` operate on JS arrays, and
 *     `case` dispatches on the injection tag.
 *   - **proof positions are irrelevant.**  The per-op irrelevant-argument mask of the kernel
 *     (`K.lookupPrim(op).irrelevant`) is honoured, so a proof argument is never even
 *     evaluated, and where a proof *is* needed as an argument (the `yes`/`no` branch of
 *     `ifLe`, the `k` of `byContra`, `fixWf`'s non-negativity proof) a single shared
 *     placeholder is passed.  Every operation is total: anything unexpected — applying a
 *     non-function, projecting a non-pair, arithmetic on a placeholder — yields the
 *     placeholder instead of throwing, so evaluating a proof can never change a result and
 *     can never throw.  The only exception is a deliberate evaluation budget
 *     (`InterpBudgetError`), which turns a non-terminating tampered term into a reportable
 *     failure instead of a hang.
 *
 * `interpTerm(term)` returns `(args) => value`; `args` correspond one-to-one to the `Lam`
 * telescope of the erased term (so a caller passes the placeholder for proof binders).
 */
import { erase, lookupPrim, type ErasedTerm, type PrimOp, type Term } from "../kernel/index";
import * as K from "../kernel/index";

// ---------------------------------------------------------------------------
// Values
// ---------------------------------------------------------------------------

/** A `Sigma` value: `Pair` erased its type annotation, so only the components remain. */
export interface IrPair {
  readonly tag: "pair";
  readonly first: IrValue;
  readonly second: IrValue;
}

/** A `Sum` value. */
export interface IrSum {
  readonly tag: "inl" | "inr";
  readonly value: IrValue;
}

/** A lambda together with the environment it closed over (de Bruijn levels). */
export interface IrClosure {
  readonly tag: "closure";
  readonly body: ErasedTerm;
  readonly env: readonly IrValue[];
}

/**
 * The induction hypothesis produced by `fixWf`: it consumes three arguments (the new state,
 * its non-negativity proof and the decrease proof) before it recurses; extra arguments (a
 * recursive function's preconditions, a loop's invariant) are applied to the result.
 */
export interface IrFixpoint {
  readonly tag: "fixpoint";
  readonly step: IrValue;
  readonly args: readonly IrValue[];
}

/** A proof, a type, a universe — anything the interpreter must not look inside. */
export interface IrProof {
  readonly tag: "proof";
}

export type IrValue =
  | bigint
  | boolean
  | string
  | readonly IrValue[]
  | IrPair
  | IrSum
  | IrClosure
  | IrFixpoint
  | IrProof;

/** The single placeholder value used for every proof position. */
export const proof: IrProof = Object.freeze({ tag: "proof" });

/** True when a value is a JS array, that is a `Vec`. */
export const isVector = (value: IrValue): value is readonly IrValue[] => Array.isArray(value);

/** True for the compound (non-array, non-primitive) values; narrows a union member away. */
const isCompound = (
  value: IrValue,
): value is IrClosure | IrFixpoint | IrPair | IrSum | IrProof =>
  typeof value === "object" && value !== null && !isVector(value);

export const isProof = (value: IrValue): value is IrProof => isCompound(value) && value.tag === "proof";

export const isPair = (value: IrValue): value is IrPair => isCompound(value) && value.tag === "pair";

export const isSum = (value: IrValue): value is IrSum => isCompound(value) && value.tag === "inl";

export const pair = (first: IrValue, second: IrValue): IrPair => ({ tag: "pair", first, second });
export const inl = (value: IrValue): IrSum => ({ tag: "inl", value });
export const inr = (value: IrValue): IrSum => ({ tag: "inr", value });

/**
 * Encode variant `index` of a union of `count` variants as a right-nested `Sum`, the way
 * `src/extract/fragment.ts` maps a union alias: `Sum V0 (Sum V1 … Vn)`, so variant `i` is
 * `i` injections of `inr` around an `inl` — and the **last** variant is the final component
 * itself, with no `inl` at all.
 */
export function encodeSum(index: number, count: number, record: IrValue): IrValue {
  if (index < 0 || index >= count) return proof;
  let out = index === count - 1 ? record : inl(record);
  for (let i = 0; i < index; i += 1) out = inr(out);
  return out;
}

/** The variant index and payload of a right-nested `Sum` value of `count` variants. */
export function decodeSum(value: IrValue, count: number): { index: number; payload: IrValue } | undefined {
  if (count <= 0) return undefined;
  let index = 0;
  let current = value;
  while (index < count - 1 && isCompound(current) && current.tag === "inr") {
    index += 1;
    current = current.value;
  }
  if (index === count - 1) return { index, payload: current };
  if (isCompound(current) && current.tag === "inl") return { index, payload: current.value };
  return undefined;
}

/** Walk a `ResultLayout`-style `fst`/`snd` path (`0` = first, `1` = second). */
export function projectPath(value: IrValue, path: readonly number[]): IrValue {
  let out = value;
  for (const step of path) {
    if (!isPair(out)) return proof;
    out = step === 0 ? out.first : out.second;
  }
  return out;
}

/** A short, readable rendering of an interpreted value, for diagnostics. */
export function showValue(value: IrValue, depth = 3): string {
  if (typeof value === "bigint") return value.toString();
  if (typeof value === "boolean") return value ? "true" : "false";
  if (typeof value === "string") return JSON.stringify(value);
  if (isVector(value)) {
    if (depth <= 0) return "[…]";
    return `[${value.map((entry) => showValue(entry, depth - 1)).join(", ")}]`;
  }
  switch (value.tag) {
    case "proof":
      return "<proof>";
    case "pair":
      return depth <= 0 ? "<pair>" : `⟨${showValue(value.first, depth - 1)}, ${showValue(value.second, depth - 1)}⟩`;
    case "inl":
    case "inr":
      return depth <= 0 ? `<${value.tag}>` : `${value.tag}(${showValue(value.value, depth - 1)})`;
    case "closure":
      return "<closure>";
    case "fixpoint":
      return "<fixpoint>";
  }
}

// ---------------------------------------------------------------------------
// Globals (`Const`)
// ---------------------------------------------------------------------------

/**
 * The definitions `Const` names resolve to: the elaborated bodies of certified functions,
 * the prelude definitions, and whatever else the caller can supply.  A `Term` is erased on
 * the way in, so a caller can hand over the environment's declarations unchanged.
 */
export class GlobalTable {
  private readonly terms = new Map<string, ErasedTerm>();

  constructor(entries: Iterable<readonly [string, ErasedTerm | Term]> = []) {
    for (const [name, term] of entries) this.define(name, term);
  }

  define(name: string, term: ErasedTerm | Term): this {
    this.terms.set(name, asErased(term));
    return this;
  }

  has(name: string): boolean {
    return this.terms.has(name);
  }

  get(name: string): ErasedTerm | undefined {
    return this.terms.get(name);
  }

  get size(): number {
    return this.terms.size;
  }

  names(): string[] {
    return [...this.terms.keys()];
  }
}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

/** Raised when a single interpretation exceeds its step budget (a non-terminating term). */
export class InterpBudgetError extends Error {
  constructor(readonly maxSteps: number) {
    super(`interpretation exceeded its budget of ${maxSteps} steps`);
    this.name = "InterpBudgetError";
  }
}

export interface InterpOptions {
  /** Definitions for `Const` names.  Unknown names become the proof placeholder. */
  readonly globals?: GlobalTable;
  /** Maximum evaluation steps per `run`; defaults to `DEFAULT_MAX_STEPS`. */
  readonly maxSteps?: number;
}

/** Enough for the examples (200 inputs of `sumTo(1000)` need a few hundred thousand). */
export const DEFAULT_MAX_STEPS = 5_000_000;

const NO_MASK: readonly number[] = [];

/** The first tag that only an unerased `Term` can have; used to detect a raw kernel term. */
function asErased(term: ErasedTerm | Term): ErasedTerm {
  if (term.tag === "Sort" || term.tag === "Pi" || term.tag === "Sigma" || term.tag === "Farkas") {
    return erase(term);
  }
  // Every other tag is structurally an `ErasedTerm`; a `Term`'s extra fields (a lambda's
  // domain, a `Prim`'s level) are simply never read.  A nested `Sort`/`Farkas` left inside is
  // handled by the interpreter's default case, which yields the proof placeholder.
  return term as ErasedTerm;
}

class Interp {
  private readonly globals: GlobalTable;
  private readonly maxSteps: number;
  private readonly globalValues = new Map<string, IrValue>();
  private readonly inProgress = new Set<string>();
  private steps = 0;

  constructor(options: InterpOptions) {
    this.globals = options.globals ?? new GlobalTable();
    this.maxSteps = options.maxSteps ?? DEFAULT_MAX_STEPS;
  }

  /** Apply a (closed) term to one value per `Lam`; the step budget restarts per call. */
  run(term: ErasedTerm, args: readonly IrValue[]): IrValue {
    this.steps = 0;
    let out = this.evalTerm(term, []);
    for (const arg of args) out = this.apply(out, arg);
    return out;
  }

  private tick(): void {
    this.steps += 1;
    if (this.steps > this.maxSteps) throw new InterpBudgetError(this.maxSteps);
  }

  private evalTerm(term: ErasedTerm, env: readonly IrValue[]): IrValue {
    this.tick();
    switch (term.tag) {
      case "Var": {
        const slot = env.length - 1 - term.index;
        return slot >= 0 && slot < env.length ? env[slot]! : proof;
      }
      case "Lam":
        return { tag: "closure", body: term.body, env };
      case "App": {
        const fn = this.evalTerm(term.fn, env);
        const arg = this.evalTerm(term.arg, env);
        return this.apply(fn, arg);
      }
      case "Pair":
        return pair(this.evalTerm(term.first, env), this.evalTerm(term.second, env));
      case "Fst": {
        const value = this.evalTerm(term.pair, env);
        return isPair(value) ? value.first : proof;
      }
      case "Snd": {
        const value = this.evalTerm(term.pair, env);
        return isPair(value) ? value.second : proof;
      }
      case "Let": {
        const value = this.evalTerm(term.value, env);
        return this.evalTerm(term.body, [...env, value]);
      }
      case "Const":
        return this.globalValue(term.name);
      case "IntLit":
        return term.value;
      case "Prim":
        return this.prim(term.op, term.args, env);
      default:
        return proof;
    }
  }

  private globalValue(name: string): IrValue {
    const cached = this.globalValues.get(name);
    if (cached !== undefined) return cached;
    const term = this.globals.get(name);
    if (term === undefined) return proof;
    // A self-referential `Const` (mutual recursion) must not loop: report it as a proof.
    if (this.inProgress.has(name)) return proof;
    this.inProgress.add(name);
    try {
      const value = this.evalTerm(term, []);
      this.globalValues.set(name, value);
      return value;
    } finally {
      this.inProgress.delete(name);
    }
  }

  private apply(fn: IrValue, arg: IrValue): IrValue {
    if (isCompound(fn)) {
      if (fn.tag === "closure") return this.evalTerm(fn.body, [...fn.env, arg]);
      if (fn.tag === "fixpoint") return this.applyFixpoint(fn, arg);
    }
    // Applying a proof, a number, a vector or a pair: a proof position we never need.
    return proof;
  }

  private applyFixpoint(fn: IrFixpoint, arg: IrValue): IrValue {
    const args = [...fn.args, arg];
    if (args.length < 3) return { tag: "fixpoint", step: fn.step, args };
    const state = args[0]!;
    const ih: IrFixpoint = { tag: "fixpoint", step: fn.step, args: [] };
    let out = this.apply(this.apply(fn.step, state), proof);
    out = this.apply(out, ih);
    for (const extra of args.slice(3)) out = this.apply(out, extra);
    return out;
  }

  private prim(op: PrimOp, args: readonly ErasedTerm[], env: readonly IrValue[]): IrValue {
    const info = lookupPrim(op);
    const mask = info?.irrelevant ?? NO_MASK;
    // Only the arguments the result depends on are evaluated; a proof argument is never
    // forced (section 6.8: evaluating a proof must not change the outcome, and must not throw).
    const arg = (index: number): IrValue => {
      if (mask.includes(index)) return proof;
      const term = args[index];
      return term === undefined ? proof : this.evalTerm(term, env);
    };
    const num = (index: number): bigint | undefined => {
      const value = arg(index);
      return typeof value === "bigint" ? value : undefined;
    };
    const branch = (fn: IrValue): IrValue => this.apply(fn, proof);

    switch (op) {
      case K.OP_ADD: {
        const a = num(0);
        const b = num(1);
        return a === undefined || b === undefined ? proof : a + b;
      }
      case K.OP_SUB: {
        const a = num(0);
        const b = num(1);
        return a === undefined || b === undefined ? proof : a - b;
      }
      case K.OP_NEG: {
        const a = num(0);
        return a === undefined ? proof : -a;
      }
      case K.OP_MUL_CONST: {
        const k = num(0);
        const e = num(1);
        return k === undefined || e === undefined ? proof : k * e;
      }
      case K.OP_DIV_FLOOR: {
        const e = num(0);
        const k = num(1);
        return e === undefined || k === undefined || k <= 0n ? proof : floorDiv(e, k);
      }
      case K.OP_DIV_TRUNC: {
        const e = num(0);
        const k = num(1);
        return e === undefined || k === undefined || k <= 0n ? proof : e / k;
      }
      case K.OP_IF_LE: {
        // `ifLe A a b yes no`: take `yes` when `a <= b`.  When a side is a placeholder the
        // result is a proof, so either branch is as good as the other; pick `yes`.
        const a = num(1);
        const b = num(2);
        const takeYes = a === undefined || b === undefined || a <= b;
        return branch(takeYes ? arg(3) : arg(4));
      }
      case K.OP_LEN: {
        const n = num(1);
        return n === undefined ? proof : n;
      }
      case K.OP_GET: {
        const vector = arg(2);
        const index = num(3);
        if (isVector(vector) && index !== undefined && index >= 0n && index < BigInt(vector.length)) {
          return vector[Number(index)]!;
        }
        return proof;
      }
      case K.OP_APPEND: {
        const u = arg(3);
        const w = arg(4);
        return isVector(u) && isVector(w) ? [...u, ...w] : proof;
      }
      case K.OP_SLICE: {
        const vector = arg(2);
        const from = num(3);
        const to = num(4);
        if (isVector(vector) && from !== undefined && to !== undefined) {
          const start = Number(from);
          const end = Number(to);
          return vector.slice(Math.max(0, start), Math.max(0, end));
        }
        return proof;
      }
      case K.OP_CAST_VEC:
        return arg(4);
      case K.OP_INL:
      case K.OP_INR: {
        const value = arg(2);
        return op === K.OP_INL ? inl(value) : inr(value);
      }
      case K.OP_CASE: {
        const scrutinee = arg(5);
        if (isCompound(scrutinee)) {
          if (scrutinee.tag === "inl") return this.apply(arg(3), scrutinee.value);
          if (scrutinee.tag === "inr") return this.apply(arg(4), scrutinee.value);
        }
        return proof;
      }
      case K.OP_FIX_WF: {
        // `fixWf A B m step x p` computes `step x p (ih)`, with `ih` recursing on a smaller
        // measure.  `A`, `B`, `m` and `p` carry no runtime content.
        const step = arg(3);
        const state = arg(4);
        const ih: IrFixpoint = { tag: "fixpoint", step, args: [] };
        let out = this.apply(step, state);
        out = this.apply(out, proof);
        return this.apply(out, ih);
      }
      case K.OP_J:
        // The only computation rule of `Eq`: `J` on a proof reduces to its base case.  Every
        // proof is the placeholder here, so the base case is the total choice.
        return arg(3);
      default:
        // `byContra`, `intEq`, `refl`, `absurd`, the primitive lemmas (`vecBounds`,
        // `divFloorSpec`, `divTruncSpec*`), `tt`, and every type former: no runtime content.
        return proof;
    }
  }
}

/** `floor(e / k)` on bigints (JS bigint division truncates towards zero). */
function floorDiv(e: bigint, k: bigint): bigint {
  const q = e / k;
  return e % k !== 0n && e < 0n !== k < 0n ? q - 1n : q;
}

/**
 * Interpret a term with proofs erased.  The result is a function of one argument per binder
 * of the term's `Lam` telescope, in order; pass `proof` for the proof binders.
 */
export function interpTerm(
  term: ErasedTerm | Term,
  options: InterpOptions = {},
): (args: readonly IrValue[]) => IrValue {
  const host = new Interp(options);
  const erased = asErased(term);
  return (args: readonly IrValue[]) => host.run(erased, args);
}

/** How many leading lambdas a term has: the number of arguments `interpTerm` expects. */
export function lambdaArity(term: ErasedTerm | Term): number {
  let current = asErased(term);
  let arity = 0;
  while (current.tag === "Lam") {
    arity += 1;
    current = current.body;
  }
  return arity;
}
