/**
 * Semantic values, closures, neutral values, and the primitive-op interface.
 *
 * Normalization by evaluation: `eval.ts` maps terms to these values, `quote.ts` reads
 * them back. Values are weak-head normalized by construction: beta and delta are
 * performed eagerly, so a value is never a redex. A primitive that cannot reduce (for
 * example `get A n v i p`, or `fixWf`) becomes a *neutral* value whose head is the
 * saturated primitive; applying more arguments extends its spine.
 *
 * `PrimInfo`/`ReduceCtx` live here rather than in `builtins.ts` so that `builtins.ts` can
 * describe reduction rules without importing `eval.ts` (which imports `builtins.ts`).
 * The registry itself is `PRIMS` in `builtins.ts`.
 */
import type { Level, PrimOp, Term } from "./term";

/**
 * A value of function or type-family type: a term body plus the value environment it was
 * created in. Applying it means evaluating the body in that environment extended with the
 * argument; that needs the global `Env`, so closure application lives in `eval.ts`.
 */
export interface Closure {
  readonly name: string;
  readonly body: Term;
  readonly env: readonly Value[];
}

/**
 * One atom of a linear form: a canonical key, its non-zero integer coefficient, and a
 * *representative* value whose canonical key is exactly `key`.
 *
 * The key is what conversion and `farkas.ts` compare; the representative exists only so
 * that `quote.ts` can read a linear value back as a term (a key string cannot be turned
 * back into a value on its own). Two atoms with the same key are always convertible, so
 * keeping the first representative is enough.
 */
export interface LinearAtom {
  readonly key: string;
  readonly coefficient: bigint;
  readonly repr: Value;
}

/**
 * A linear form: a constant plus a map from atom key to atom, with no zero coefficients.
 * `LinearValue` is the same thing as a value of type `Int`.
 */
export interface LinearForm {
  readonly k: bigint;
  readonly atoms: ReadonlyMap<string, LinearAtom>;
}

/**
 * A linear value of type `Int`, i.e. a linear form. See `linear.ts` for how keys are
 * computed.
 */
export interface LinearValue extends LinearForm {
  readonly tag: "Linear";
}

/** The head of a neutral value. */
export type Head =
  | { readonly tag: "Var"; readonly level: Level }
  | { readonly tag: "Const"; readonly name: string }
  | { readonly tag: "Prim"; readonly op: PrimOp; readonly level: Level; readonly args: readonly Value[] }
  | { readonly tag: "Fst"; readonly pair: Value }
  | { readonly tag: "Snd"; readonly pair: Value };

export type NeutralValue = { readonly tag: "Neutral"; readonly head: Head; readonly spine: readonly Value[] };

export type Value =
  | { readonly tag: "Sort"; readonly level: Level }
  | { readonly tag: "Pi"; readonly name: string; readonly domain: Value; readonly codomain: Closure }
  | { readonly tag: "Lam"; readonly name: string; readonly domain: Value; readonly body: Closure }
  | { readonly tag: "Sigma"; readonly name: string; readonly first: Value; readonly second: Closure }
  | { readonly tag: "Pair"; readonly sigma: Value; readonly first: Value; readonly second: Value }
  | { readonly tag: "IntLit"; readonly value: bigint }
  /**
   * A value of type `Int` that is not a literal: `k + Σ cᵢ · xᵢ` over atom keys. Every
   * value built from literals with `add`, `sub`, `neg` and `mulConst` reduces to one of
   * these (`IntLit` is the atom-free case), and conversion of `Int` values compares linear
   * forms. Milestone 2 had only `IntLit`.
   */
  | LinearValue
  /**
   * A checked Farkas certificate, the only way to inhabit `Empty`. It is a proof, never
   * computed with: `absurd` has no reduction rule, and one cannot eliminate `Empty` into
   * a value. Conversion treats all certificates as equal (both have type `Empty`, and all
   * proofs of a proposition are interchangeable for the kernel's purposes).
   */
  | { readonly tag: "Farkas"; readonly hyps: readonly Term[]; readonly coeffs: readonly bigint[] }
  | NeutralValue;

// ---------------------------------------------------------------------------
// Value constructors
// ---------------------------------------------------------------------------

export const vsort = (level: Level): Value => ({ tag: "Sort", level });

export const vint = (value: bigint): Value => ({ tag: "IntLit", value });

/**
 * A linear value: drops zero coefficients, and returns a plain `IntLit` when no atom is
 * left, so that "atom-free linear value" and "literal" are the same value everywhere.
 */
export function vlinear(k: bigint, atoms: ReadonlyMap<string, LinearAtom>): Value {
  const kept = new Map<string, LinearAtom>();
  for (const [key, atom] of atoms) {
    if (atom.coefficient !== 0n) kept.set(key, atom);
  }
  return kept.size === 0 ? vint(k) : { tag: "Linear", k, atoms: kept };
}

export const vpi = (name: string, domain: Value, codomain: Closure): Value => ({
  tag: "Pi",
  name,
  domain,
  codomain,
});

export const vlam = (name: string, domain: Value, body: Closure): Value => ({ tag: "Lam", name, domain, body });

export const vsigma = (name: string, first: Value, second: Closure): Value => ({
  tag: "Sigma",
  name,
  first,
  second,
});

export const vpair = (sigma: Value, first: Value, second: Value): Value => ({
  tag: "Pair",
  sigma,
  first,
  second,
});

export const vfarkas = (hyps: readonly Term[], coeffs: readonly bigint[]): Value => ({
  tag: "Farkas",
  hyps,
  coeffs,
});

/** A free variable at `level` (a de Bruijn *level*: globally unique in a derivation). */
export const vvar = (level: Level): NeutralValue => ({
  tag: "Neutral",
  head: { tag: "Var", level },
  spine: [],
});

export const vconst = (name: string): NeutralValue => ({
  tag: "Neutral",
  head: { tag: "Const", name },
  spine: [],
});

/** A saturated but stuck primitive, e.g. `get A n v i p` or `fixWf A B m step`. */
export const vprim = (op: PrimOp, level: Level, args: readonly Value[]): NeutralValue => ({
  tag: "Neutral",
  head: { tag: "Prim", op, level, args },
  spine: [],
});

export const vfst = (pair: Value): NeutralValue => ({ tag: "Neutral", head: { tag: "Fst", pair }, spine: [] });

export const vsnd = (pair: Value): NeutralValue => ({ tag: "Neutral", head: { tag: "Snd", pair }, spine: [] });

/** Extends the application spine of a neutral value. */
export const extendSpine = (neutral: NeutralValue, arg: Value): NeutralValue => ({
  tag: "Neutral",
  head: neutral.head,
  spine: [...neutral.spine, arg],
});

/** The saturated, spine-free primitive constructor a value is, if any. */
export function constructorHead(value: Value): { op: PrimOp; level: Level; args: readonly Value[] } | undefined {
  if (value.tag !== "Neutral" || value.spine.length !== 0) return undefined;
  return value.head.tag === "Prim" ? value.head : undefined;
}

/** The head of a neutral value, if it is one. */
export function neutralHead(value: Value): Head | undefined {
  return value.tag === "Neutral" ? value.head : undefined;
}

// ---------------------------------------------------------------------------
// Primitive ops
// ---------------------------------------------------------------------------

/** What a reduction rule can ask of the evaluator it runs under. */
export interface ReduceCtx {
  /** Apply a function value to an argument value (performs beta on a `Lam`). */
  apply: (fn: Value, arg: Value) => Value;
  /** Evaluate a term in a value environment (levels 0..n-1 map to `env[0..n-1]`). */
  evalIn: (term: Term, env: readonly Value[]) => Value;
  /** The definition of a global name, for rules that unfold definitions. */
  lookup: (name: string) => GlobalInfo | undefined;
}

/** The part of a global declaration a reduction rule may inspect. */
export type GlobalInfo =
  | { readonly kind: "def"; readonly value: Term; readonly opaque: boolean }
  | { readonly kind: "axiom" }
  | { readonly kind: "external" };

/**
 * Everything the kernel knows about one primitive op.
 *
 * - `typeFor(level)` returns the op's type as a closed Pi telescope over its arguments.
 *   `check.ts` walks that telescope to type a `Prim` term, which is how the ops that
 *   mention `Type l` (`absurd`, `case`, `J`, and milestone 3's `fixWf`) get their level.
 * - `reduce` returns `undefined` for "stuck": the op then stays a neutral value. `fixWf`
 *   is opaque precisely by having no `reduce`.
 * - `irrelevant` lists 0-based argument positions that conversion ignores (proof
 *   irrelevance) and that atom keys erase. `convArgs` is a full custom conversion rule
 *   (`Le` in milestone 3); returning `undefined` means "compare argument-wise, skipping
 *   `irrelevant` positions".
 * - `positiveLiteralArgs` lists 0-based positions that `check.ts` requires to be a
 *   *positive integer literal* term. It exists for one reason only: `divFloor`/`divTrunc`
 *   and their spec lemmas are trusted for `k > 0`, so a variable or non-positive divisor
 *   would make the built-in lemmas assert something false.
 */
export interface PrimInfo {
  readonly name: PrimOp;
  readonly arity: number;
  readonly typeFor: (level: Level) => Term;
  readonly reduce?: (args: readonly Value[], ctx: ReduceCtx) => Value | undefined;
  readonly irrelevant?: readonly number[];
  readonly convArgs?: (a: readonly Value[], b: readonly Value[]) => boolean | undefined;
  readonly positiveLiteralArgs?: readonly number[];
}
