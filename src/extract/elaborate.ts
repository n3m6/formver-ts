/**
 * The elaborator (specification 6.3, milestone 7).
 *
 * `elaborateFunction` turns one `FunctionIR` into a kernel term of its `signature.type`:
 *
 *   - a lambda telescope over `signature.binders`,
 *   - the body statements walked in tail position, with `Let` for locals, `ifLe` for
 *     comparisons on `Int` and `case` for union discriminants (each branch hypothesis in
 *     scope),
 *   - `get`/`slice`/`append`/call terms built with the proofs of their obligation sites,
 *   - `return` packed into the `ResultLayout`'s `Sigma`, carrying the certified `InRange`
 *     proof and the postcondition proofs.
 *
 * Every `ObligationSite` becomes an `Obligation`, certified in the elaborator's own context
 * (with `context` supplied, so `certify` self-checks against the kernel).  A hole whose goal
 * is literally a hypothesis in scope is filled without Z3.  Sites are certified in source
 * order as the walk reaches them, so a later goal may use an earlier site's proof.
 *
 * The elaborator is untrusted: the only thing that makes a function `certified` is
 * `K.checkType(env, term, type)` accepting the completed term, and only then is the function
 * added to the environment as a `def`.  Nothing here throws: every failure becomes a located
 * diagnostic.
 *
 * Part A (this milestone) covers straight-line code, `if`/`switch`/ternary/narrowing,
 * returns, calls, arithmetic and `index`/`slice`/`append`.  Loops and recursive functions
 * are part B: they are reported as `failed` with a clearly-worded `internal` diagnostic
 * rather than crashing.
 */
import { sortDiagnostics, type Diagnostic, type Span } from "../diagnostics";
import * as K from "../kernel/index";
import type { Term } from "../kernel/index";
import { certify } from "../vc/certify";
import { contextAtomNames, type Obligation } from "../vc/obligations";
import {
  Ids,
  deBruijnIndex,
  exprTerm,
  project,
  slotTerm,
  type Binder,
  type CalleeIR,
  type CondIR,
  type Ctx,
  type ExprIR,
  type FactIR,
  type FunctionIR,
  type ImportedSpec,
  type LoopIR,
  type ObligationKind,
  type ObligationSite,
  type SignatureIR,
  type Slot,
  type StmtIR,
  type TermOptions,
  type TypeIR,
  type UnionIR,
  type VariantIR,
} from "./fragment";
import { shiftTerm } from "./prelude";

// ---------------------------------------------------------------------------
// Result shapes
// ---------------------------------------------------------------------------

/** Status of one obligation site. */
export type ObligationStatus = "certified" | "smt-only" | "failed";

export interface ObligationOutcome {
  readonly siteId: number;
  readonly kind: ObligationKind;
  readonly span: Span;
  /** The goal as the extractor rendered it, for diagnostics. */
  readonly text: string;
  readonly status: ObligationStatus;
  readonly reason?: string;
  readonly path?: readonly string[];
  readonly counterexample?: Readonly<Record<string, string>>;
}

export type FunctionStatus = "certified" | "smt-only" | "failed";

export interface FunctionElaboration {
  readonly name: string;
  readonly status: FunctionStatus;
  readonly certified: boolean;
  /** The completed kernel term, when the kernel accepted it. */
  readonly term?: Term;
  /** `signature.type`. */
  readonly type: Term;
  readonly obligations: readonly ObligationOutcome[];
  readonly diagnostics: readonly Diagnostic[];
  /** Imported specs this function's body used. */
  readonly imports: readonly ImportedSpec[];
  /** Names of functions whose spec was used although they are not certified. */
  readonly dependsOnUncertified: readonly string[];
}

export interface ElaborateOptions {
  /** Per-obligation Z3 timeout. */
  readonly timeoutMs?: number;
  /** Names (imported or local) known not to be certified. */
  readonly uncertified?: ReadonlySet<string>;
  /** Every function of the same file, by name (a local call needs the callee's signature). */
  readonly functions?: ReadonlyMap<string, FunctionIR>;
  /** sha256 of the source, recorded on an `external` declaration of an uncertified function. */
  readonly sourceHash?: string;
  /**
   * Admit a function that is not certified as an `external` declaration, so its callers can
   * still be elaborated (lenient mode).  Strict mode leaves the environment untouched.
   */
  readonly admitUncertified?: boolean;
  /**
   * `false` when no SMT solver is available (the section 4.4 "libz3 is missing" rule): every
   * obligation is then reported as `smt-only` — "not discharged, a runtime check is needed" —
   * instead of failing with a solver error, and the function is never kernel-certified.
   */
  readonly solver?: boolean;
}

/** Why an obligation is `smt-only` when the solver was never asked (section 4.4). */
export const NO_SOLVER_REASON = "no SMT solver is available";

export interface ElaborationOutcome {
  readonly result: FunctionElaboration;
  /** The environment with the function's declaration added (definition or external). */
  readonly env: K.Env;
  /** Set when the declaration could not be added. */
  readonly declarationError?: Diagnostic;
}

/** Thrown inside the elaborator when the IR does not determine a kernel term. */
class ElaborateFailure extends Error {}

/**
 * Ids for the binders this module synthesises (the value bound for a `@post`, the
 * hypotheses of a case split).  They are **negative** so that they can never collide with
 * the extractor's per-file ids, which start at 1: `deBruijnIndex` and `sameSlot` compare
 * binders by id, and a collision would silently address the wrong variable.
 */
let syntheticId = 0;
function freshId(): number {
  syntheticId -= 1;
  return syntheticId;
}



function pushed(ctx: Ctx, binder: Binder): Ctx {
  return { ...ctx, binders: [...ctx.binders, binder] };
}// ---------------------------------------------------------------------------
// Slots
// ---------------------------------------------------------------------------

function sameSlot(a: Slot, b: Slot): boolean {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "binder":
      return b.kind === "binder" && a.binder.id === b.binder.id;
    case "state":
      return b.kind === "state" && a.state.id === b.state.id && a.path.join(",") === b.path.join(",");
    case "payload":
      return b.kind === "payload" && a.payload.id === b.payload.id;
    case "result":
      return true;
  }
}

/** Rewrite every `Slot` of an expression (including a nested condition's tag-test subject). */
function mapSlots(e: ExprIR, f: (slot: Slot) => Slot): ExprIR {
  const slot = e.slot === undefined ? undefined : f(e.slot);
  const args = e.args.map((arg) => mapSlots(arg, f));
  const vecLength = e.vecLength === undefined ? undefined : mapSlots(e.vecLength, f);
  let cond = e.cond;
  if (cond !== undefined) {
    cond = {
      ...cond,
      tagTest:
        cond.tagTest === undefined ? undefined : { ...cond.tagTest, subject: f(cond.tagTest.subject) },
      thenExpr: cond.thenExpr === undefined ? undefined : mapSlots(cond.thenExpr, f),
      elseExpr: cond.elseExpr === undefined ? undefined : mapSlots(cond.elseExpr, f),
      expr: mapSlots(cond.expr, f),
    };
  }
  return { ...e, args, vecLength, cond, slot };
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/** `(p1) -> (p2) -> … -> rest`, the motive of a case split that eliminates preconditions. */
function arrowsTo(propositions: readonly Term[], rest: Term): Term {
  let out = rest;
  for (let i = propositions.length - 1; i >= 0; i -= 1) out = K.pi("_", propositions[i]!, out);
  return out;
}

/**
 * `(h0 : p0) -> (h1 : p1) -> … -> rest`, where every proposition and `rest` are given in the
 * *same* context: `pᵢ` is lifted past the `i` binders before it and `rest` past all of them.
 * (`arrowsTo` instead expects propositions that are already in the scope of the earlier
 * binders.)
 */
function arrowStack(propositions: readonly Term[], rest: Term): Term {
  let out = shiftTerm(rest, propositions.length);
  for (let i = propositions.length - 1; i >= 0; i -= 1) {
    out = K.pi(`h${i}`, shiftTerm(propositions[i]!, i), out);
  }
  return out;
}

/** `body[Var 0 := arg]`, with `body` under one binder more than `arg`. */
function instantiateTop(body: Term, arg: Term): Term {
  return walk(body, 0);

  function walk(t: Term, depth: number): Term {
    switch (t.tag) {
      case "Var": {
        const free = t.index - depth;
        if (free < 0) return t;
        if (free === 0) return shiftTerm(arg, depth);
        return { tag: "Var", index: t.index - 1 };
      }
      case "Sort":
      case "IntLit":
      case "Const":
        return t;
      case "Pi":
        return { tag: "Pi", name: t.name, domain: walk(t.domain, depth), body: walk(t.body, depth + 1) };
      case "Lam":
        return { tag: "Lam", name: t.name, domain: walk(t.domain, depth), body: walk(t.body, depth + 1) };
      case "Sigma":
        return { tag: "Sigma", name: t.name, first: walk(t.first, depth), second: walk(t.second, depth + 1) };
      case "Let":
        return {
          tag: "Let",
          name: t.name,
          type: walk(t.type, depth),
          value: walk(t.value, depth),
          body: walk(t.body, depth + 1),
        };
      case "App":
        return { tag: "App", fn: walk(t.fn, depth), arg: walk(t.arg, depth) };
      case "Pair":
        return { tag: "Pair", sigma: walk(t.sigma, depth), first: walk(t.first, depth), second: walk(t.second, depth) };
      case "Fst":
        return { tag: "Fst", pair: walk(t.pair, depth) };
      case "Snd":
        return { tag: "Snd", pair: walk(t.pair, depth) };
      case "Prim":
        return t.level === undefined
          ? { tag: "Prim", op: t.op, args: t.args.map((arg) => walk(arg, depth)) }
          : { tag: "Prim", op: t.op, level: t.level, args: t.args.map((arg) => walk(arg, depth)) };
      case "Farkas":
        return { tag: "Farkas", hyps: t.hyps.map((hyp) => walk(hyp, depth)), coeffs: t.coeffs };
    }
  }
}

/**
 * True when this expression builds a kernel term that carries proof arguments (a call, an
 * indexed read, a slice or a spread): those terms have to be bound with a `let` before a
 * postcondition mentions them (see `bindReturnValue`).
 */
function containsProofCarrier(e: ExprIR): boolean {
  if (e.kind === "index" || e.kind === "slice" || e.kind === "append") return true;
  // A call is *bound* first (`elabExpr`), so its term is a plain variable by the time a
  // return value or a fact mentions it; a prelude call (`divFloor`, `ifLe`) is a kernel
  // definition and needs no obligation proof at all.
  if (e.kind === "call") return false;
  if (e.args.some(containsProofCarrier)) return true;
  if (e.vecLength !== undefined && containsProofCarrier(e.vecLength)) return true;
  if (e.cond !== undefined) {
    if (e.cond.thenExpr !== undefined && containsProofCarrier(e.cond.thenExpr)) return true;
    if (e.cond.elseExpr !== undefined && containsProofCarrier(e.cond.elseExpr)) return true;
  }
  return false;
}

/**
 * Replace every subterm that prints exactly like `pattern` by `replacement`.  Used to state
 * a fact about a `let`-bound variable instead of the term the fact was derived from; the
 * comparison is syntactic, which is enough because both come from the same builder.
 */
function replaceSubterm(term: Term, pattern: Term, replacement: Term): Term {
  const key = K.formatTerm(pattern);
  return visit(term, 0);

  function visit(t: Term, depth: number): Term {
    if (K.formatTerm(t) === key) return shiftTerm(replacement, depth);
    switch (t.tag) {
      case "Var":
      case "Sort":
      case "IntLit":
      case "Const":
        return t;
      case "Pi":
        return { tag: "Pi", name: t.name, domain: visit(t.domain, depth), body: visit(t.body, depth + 1) };
      case "Lam":
        return { tag: "Lam", name: t.name, domain: visit(t.domain, depth), body: visit(t.body, depth + 1) };
      case "Sigma":
        return { tag: "Sigma", name: t.name, first: visit(t.first, depth), second: visit(t.second, depth + 1) };
      case "Let":
        return {
          tag: "Let",
          name: t.name,
          type: visit(t.type, depth),
          value: visit(t.value, depth),
          body: visit(t.body, depth + 1),
        };
      case "App":
        return { tag: "App", fn: visit(t.fn, depth), arg: visit(t.arg, depth) };
      case "Pair":
        return {
          tag: "Pair",
          sigma: visit(t.sigma, depth),
          first: visit(t.first, depth),
          second: visit(t.second, depth),
        };
      case "Fst":
        return { tag: "Fst", pair: visit(t.pair, depth) };
      case "Snd":
        return { tag: "Snd", pair: visit(t.pair, depth) };
      case "Prim":
        return t.level === undefined
          ? { tag: "Prim", op: t.op, args: t.args.map((arg) => visit(arg, depth)) }
          : { tag: "Prim", op: t.op, level: t.level, args: t.args.map((arg) => visit(arg, depth)) };
      case "Farkas":
        return { tag: "Farkas", hyps: t.hyps.map((hyp) => visit(hyp, depth)), coeffs: t.coeffs };
    }
  }
}

/** `Le a a`: contradictory negation, so `byContra` with a one-row Farkas certificate. */
function leSelf(a: Term): Term {
  // The annotation of the refutation lambda is in the *outer* context: `a` keeps its index.
  return K.ByContra(a, a, K.lam("_k", K.Lt(a, a), K.Farkas([K.varTerm(0)], [1n])));
}

/**
 * `Le a b` (or `Le b a`) from `h : Eq Int a b`, by transport along the equality.  Stated
 * this way because `certify` cannot use an `Eq` hypothesis as a linear row: building that
 * proof is exactly what this does, with the de Bruijn shifts done once here.
 */
function transportLe(a: Term, b: Term, h: Term, backward: boolean): Term {
  const inner = shiftTerm(a, 2);
  const motive = K.lam(
    "b'",
    K.Int,
    K.lam(
      "_h",
      K.Eq(K.Int, shiftTerm(a, 1), K.varTerm(0)),
      backward ? K.Le(K.varTerm(1), inner) : K.Le(inner, K.varTerm(1)),
    ),
  );
  return K.J(0, K.Int, a, motive, leSelf(a), b, h);
}

/**
 * An `Eq Int a b` hypothesis as the two `Le` facts it implies.  `certify`'s own `J`
 * construction for an equality hypothesis is rejected by the kernel, so the transport is
 * built here; the equation itself is then dropped, because it can only be a row through
 * those two facts.
 */
function splitEquation(hyp: Hyp): Hyp[] | undefined {
  const term = hyp.term;
  if (term.tag !== "Prim" || term.op !== K.OP_EQ || term.args.length !== 3) return undefined;
  const type = term.args[0]!;
  if (type.tag !== "Prim" || type.op !== K.OP_INT) return undefined;
  const a = term.args[1]!;
  const b = term.args[2]!;
  return [
    { term: K.Le(a, b), proof: transportLe(a, b, hyp.proof, false), depth: hyp.depth, origin: hyp.origin },
    { term: K.Le(b, a), proof: transportLe(a, b, hyp.proof, true), depth: hyp.depth, origin: hyp.origin },
  ];
}

/** Every hypothesis, with `Eq Int` hypotheses expanded into their two `Le` consequences. */
function expandEquations(hyps: readonly Hyp[]): Hyp[] {
  const out: Hyp[] = [];
  for (const hyp of hyps) out.push(...(splitEquation(hyp) ?? [hyp]));
  return out;
}

/** Syntactic equality, used for "the goal is literally a hypothesis in scope". */
function sameTerm(a: Term, b: Term): boolean {
  return K.formatTerm(a) === K.formatTerm(b);
}

/**
 * Replace the free variables of a *closed-relative-to-the-call-site* term by the call's
 * arguments: `args` maps a free de Bruijn index (of the ambient context the term is closed
 * under) to a term of the destination context.
 */
function substituteFree(term: Term, args: ReadonlyMap<number, Term>): Term {
  return walk(term, 0);

  function walk(t: Term, depth: number): Term {
    switch (t.tag) {
      case "Var": {
        if (t.index < depth) return t;
        const argument = args.get(t.index - depth);
        if (argument === undefined) {
          throw new ElaborateFailure(`the callee mentions a binder (index ${t.index}) the call does not supply`);
        }
        return shiftTerm(argument, depth);
      }
      case "Sort":
      case "IntLit":
      case "Const":
        return t;
      case "Pi":
        return { tag: "Pi", name: t.name, domain: walk(t.domain, depth), body: walk(t.body, depth + 1) };
      case "Lam":
        return { tag: "Lam", name: t.name, domain: walk(t.domain, depth), body: walk(t.body, depth + 1) };
      case "Sigma":
        return { tag: "Sigma", name: t.name, first: walk(t.first, depth), second: walk(t.second, depth + 1) };
      case "Let":
        return {
          tag: "Let",
          name: t.name,
          type: walk(t.type, depth),
          value: walk(t.value, depth),
          body: walk(t.body, depth + 1),
        };
      case "App":
        return { tag: "App", fn: walk(t.fn, depth), arg: walk(t.arg, depth) };
      case "Pair":
        return { tag: "Pair", sigma: walk(t.sigma, depth), first: walk(t.first, depth), second: walk(t.second, depth) };
      case "Fst":
        return { tag: "Fst", pair: walk(t.pair, depth) };
      case "Snd":
        return { tag: "Snd", pair: walk(t.pair, depth) };
      case "Prim":
        return t.level === undefined
          ? { tag: "Prim", op: t.op, args: t.args.map((arg) => walk(arg, depth)) }
          : { tag: "Prim", op: t.op, level: t.level, args: t.args.map((arg) => walk(arg, depth)) };
      case "Farkas":
        return { tag: "Farkas", hyps: t.hyps.map((hyp) => walk(hyp, depth)), coeffs: t.coeffs };
    }
  }
}

// ---------------------------------------------------------------------------
// Hypotheses
// ---------------------------------------------------------------------------

/**
 * A proposition assumed at some point of the walk, with its proof.  Both terms live in a
 * context of `depth` binders; `hypAt` moves them to a deeper one.
 */
interface Hyp {
  readonly term: Term;
  readonly proof: Term;
  readonly depth: number;
  /** The IR node, when the hypothesis came from a conditional spec. */
  readonly prop?: ExprIR;
  readonly origin?: string;
}

function hypAt(hyp: Hyp, depth: number): Hyp {
  if (hyp.depth === depth) return hyp;
  if (depth < hyp.depth) {
    throw new ElaborateFailure(
      `internal: a hypothesis of depth ${hyp.depth} cannot be used at depth ${depth}`,
    );
  }
  const by = depth - hyp.depth;
  return { ...hyp, term: shiftTerm(hyp.term, by), proof: shiftTerm(hyp.proof, by), depth };
}

function hypsAt(hyps: readonly Hyp[], depth: number): Hyp[] {
  return hyps.map((hyp) => hypAt(hyp, depth));
}

/**
 * Drop repeated hypotheses.  The key is the *proposition* (and the depth), not the proof: a
 * fact the walk derived and the same fact the extractor recorded have different proofs but
 * carry the same row, and every extra row is another integer variable in the certificate
 * search.
 */
function dedupeHyps(hyps: readonly Hyp[]): Hyp[] {
  const seen = new Set<string>();
  const out: Hyp[] = [];
  for (const hyp of hyps) {
    const key = `${hyp.depth}|${K.formatTerm(hyp.term)}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(hyp);
  }
  return out;
}

/**
 * Every call node of an expression that builds a term carrying proof arguments, in
 * evaluation order (a call's arguments before the call itself), so that binding them one by
 * one lets a later call's arguments mention the earlier bound variables.
 */
function callNodesIn(e: ExprIR): ExprIR[] {
  const out: ExprIR[] = [];
  const visit = (node: ExprIR): void => {
    for (const arg of node.args) visit(arg);
    if (node.vecLength !== undefined) visit(node.vecLength);
    if (node.cond !== undefined) {
      visit(node.cond.expr);
      if (node.cond.thenExpr !== undefined) visit(node.cond.thenExpr);
      if (node.cond.elseExpr !== undefined) visit(node.cond.elseExpr);
    }
    if (node.kind === "call" && node.callee !== undefined && node.callee.kind !== "prelude") out.push(node);
  };
  visit(e);
  return out;
}

/**
 * The identity of a call *site*.  The extractor copies a call node when it records a fact
 * about its result (`instantiate`/`substituteExpr` build fresh nodes), so binding by object
 * identity would miss the copy; the source span identifies the call unambiguously.
 */
function callSiteKey(e: ExprIR): string {
  return `${e.span.line}:${e.span.col}:${e.span.offset}:${e.span.endOffset ?? ""}|${e.callee?.name ?? ""}`;
}

/** `[1] * index + [0]`: where component `index` of a nested `Sigma` tuple lives. */
function componentPath(index: number): number[] {
  return index === 0 ? [0] : [...Array(index).fill(1), 0];
}

/**
 * The `fst`/`snd` path of the `index`-th component of a right-nested `And` of `count` parts
 * (`andAll`/`conjoin` nest as `And p0 (And p1 …)`).  A single part *is* the conjunction, so
 * its path is empty — which is what a one-component `@post` or `@pre` list needs.
 */
function conjunctionProjection(index: number, count: number): number[] {
  if (count <= 1) return [];
  // The last component is the innermost `snd`: `And p0 (And p1 p2)` reaches `p2` by `snd`
  // twice, and every earlier component by `snd`s and an `fst`.
  return index === count - 1 ? Array(count - 1).fill(1) : [...Array(index).fill(1), 0];
}

// ---------------------------------------------------------------------------
// The elaborator
// ---------------------------------------------------------------------------

interface CaseBranch {
  readonly variant: VariantIR;
  /** The payload binder the extraction bound in this branch. */
  readonly binder: Binder;
  readonly build: (ctx: Ctx, hyps: readonly Hyp[]) => Term;
}

interface SolveDetail {
  readonly reason?: string;
  readonly path?: readonly string[];
  readonly counterexample?: Readonly<Record<string, string>>;
}

/** What a `continue` statement needs from the loop being elaborated. */
interface LoopContext {
  readonly loop: LoopIR;
  /** `ih`, the induction hypothesis of the loop's `step`. */
  readonly ih: Binder;
  /** The measure function `m : A -> Int`, in the context of the loop. */
  readonly measure: Term;
  /** The invariant `Inv : A -> Type 0`, in the context of the loop. */
  readonly invariant: Term;
  /** The carried variables, in tuple order. */
  readonly components: readonly Component[];
  /** The tuple telescope, for the back edge's new state. */
  readonly spec: TupleSpec;
  /** The elaborator's context depth where the loop's state tuple lives. */
  readonly stateDepth: number;
}

/** One component of a tuple (`A`): the name for the `Sigma` annotations and its path. */
interface Component {
  readonly name: string;
  /** The component's type, written at the depth `TupleSpec.typeAt` expects. */
  readonly type: Term;
  /** Its path from the tuple root: `[1] * i + [0]`. */
  readonly path: readonly number[];
}

/**
 * A tuple telescope and the rule that re-bases a component type under the telescope's own
 * binders.  A loop's component types live in the enclosing context (only a shift is needed);
 * a recursive function's are signature binder types, whose references to earlier parameters
 * become telescope variables.  Both `A` and every `Pair` annotation are built from `typeAt`,
 * which is what keeps them in step for a *dependent* component (`Vec T n_a`, `InRange n`).
 */
interface TupleSpec {
  readonly components: readonly Component[];
  /** `typeAt(ctx, bound, i)`: component `i`'s type in the scope `[ctx, v_0 … v_{bound-1}]`. */
  readonly typeAt: (ctx: Ctx, bound: number, index: number) => Term;
}

/** What the body of a recursive function needs to build a recursive call. */
interface RecursionContext {
  /** The argument tuple binder `x : A`. */
  readonly tuple: Binder;
  /** `ih`, the induction hypothesis of the `step`. */
  readonly ih: Binder;
  /** The measure function `m : A -> Int`, in the enclosing context. */
  readonly measure: Term;
  /** The signature binders the tuple holds, in component order (type parameters excluded). */
  readonly binders: readonly Binder[];
  /** The tuple telescope. */
  readonly spec: TupleSpec;
}

class Elaborator {
  private readonly env: K.Env;
  private readonly fn: FunctionIR;
  private readonly options: ElaborateOptions;
  private readonly diagnostics: Diagnostic[] = [];
  /**
   * Proof per site id, with the depth it was built at.  A site's proof is a term in the site's
   * own context; using it deeper (the `index` proof that a later `elems_a i p` fact needs, for
   * example) requires weakening it, which `proofAt` does.  A placeholder sits here for a site
   * that is not certified.
   */
  private readonly proofs = new Map<number, { readonly term: Term; readonly depth: number }>();
  /** `proofsAt` memoises one shifted view per depth; a new proof invalidates them all. */
  private readonly proofViews = new Map<number, ReadonlyMap<number, Term>>();
  private readonly outcomes = new Map<number, ObligationOutcome>();
  private readonly visited = new Set<number>();
  /** Hypotheses of the expression currently being built (the `override` hook reads this). */
  private activeHyps: readonly Hyp[] = [];
  /** Built call applications, keyed by the call node (see `callInfo`). */
  private readonly callCache = new Map<
    ExprIR,
    { depth: number; packed: Term; packedType?: Term; applied: Map<number, Term> }
  >();
  private auxCount = 0;
  private readonly dependsOnUncertified = new Set<string>();
  /** Set once an obligation was left to a runtime check because no solver is available. */
  private noSolver = false;

  /**
   * Extraction-time position of each binder the elaborator has in scope, keyed by binder id.
   *
   * The extractor's stored terms (`Binder.type`, a site's `context`) are written in the
   * context of the *preceding extractor binders*.  The elaborator's own context is in the
   * final kernel layout, which may differ: a loop binds `ih` where the extractor binds
   * `hinv`, and a recursive function substitutes its parameters by a tuple.  The recorded
   * position is what `fromExtractor` renames by, so a stored term never has to be trusted
   * to have the same layout.
   */
  private readonly extOf = new Map<number, number>();
  /** Binders whose `type` this module built itself (never in the extractor's layout). */
  private readonly ownType = new Set<number>();
  /**
   * Binders whose every *use* is replaced by a value: a `let` local whose value carries no
   * proof argument (so a fact about the value lines up with a goal), and a recursive
   * function's parameters (replaced by a projection of the argument tuple).
   */
  private readonly inlineSlots = new Map<number, (ctx: Ctx) => Term | undefined>();
  /**
   * The extractor's position of such a binder, when stored *terms* that mention it must be
   * substituted too (a recursive function's parameters).  A `let` local is left alone here:
   * it is still a real variable in the kernel context.
   */
  private readonly inlineExt = new Map<number, (ctx: Ctx) => Term | undefined>();
  /**
   * Proof-carrying calls this statement has bound with a `let`, so that a goal or a fact
   * mentions the *variable* rather than a term full of certificates.  Without this, the atom
   * of a recursive call's value carries the proof arguments of the call, which the SMT
   * encoding cannot read (and which makes a `Sigma` look dependent when it is not).
   */
  private readonly boundCalls = new Map<
    string,
    { readonly binder: Binder; readonly depth: number; readonly applied: Map<number, Term> }
  >();
  /** The loop whose body is being elaborated (a `continue` needs its `ih`). */
  private readonly loopStack: LoopContext[] = [];
  /** A recursive function's argument tuple (`x`), while its body is elaborated. */
  private recursion: RecursionContext | null = null;

  constructor(env: K.Env, fn: FunctionIR, options: ElaborateOptions) {
    this.env = env;
    this.fn = fn;
    this.options = options;
  }

  // ---- entry point --------------------------------------------------------

  run(): ElaborationOutcome {
    // The signature binders are the extractor's first binders: record their positions so a
    // stored term that mentions one can be renamed into the elaborator's own context.
    this.fn.signature.binders.forEach((binder, position) => this.extOf.set(binder.id, position));
    const ctx: Ctx = { binders: this.fn.signature.binders, facts: [], narrowings: [], ids: new Ids() };

    const hyps = this.signatureHyps(ctx);

    let body: Term;
    try {
      // A recursive function's body is the `step` of a `fixWf` over its own parameters; a
      // straight-line one is the body itself.
      body = this.fn.recursive ? this.elabRecursive(ctx, hyps) : this.elabStmts(ctx, hyps, this.fn.body);
      this.sweep(ctx, hyps);
    } catch (error) {
      this.internal(
        this.fn.nameSpan,
        `could not elaborate \`${this.fn.name}\`: ${error instanceof Error ? error.message : String(error)}`,
      );
      return this.finish("failed");
    }
    return this.admit(body);
  }

  /** Wrap the body in the signature's lambda telescope and deliver the verdict. */
  private admit(body: Term): ElaborationOutcome {
    let term = body;
    for (let i = this.fn.signature.binders.length - 1; i >= 0; i -= 1) {
      const binder = this.fn.signature.binders[i]!;
      term = K.lam(binder.name, binder.type, term);
    }

    const failed = [...this.outcomes.values()].some((o) => o.status === "failed");
    if (failed) return this.finish("failed", term);

    const smtOnly = this.noSolver || [...this.outcomes.values()].some((o) => o.status === "smt-only");
    const checked = K.checkType(this.env, term, this.fn.signature.type);
    if (!checked.ok) {
      if (smtOnly) return this.finish("smt-only", term);
      this.internal(
        this.fn.nameSpan,
        `the kernel rejected the elaborated term of \`${this.fn.name}\`: ${K.formatKernelError(checked.error)}` +
          (checked.error.term === undefined ? "" : ` || at ${K.formatTerm(checked.error.term)}`),
      );
      return this.finish("failed", term);
    }
    return this.finish(smtOnly ? "smt-only" : "certified", term);
  }

  // ---- extractor layouts --------------------------------------------------

  /**
   * A term stored by the extractor, whose free variables refer to the first `extDepth`
   * extractor binders, as a term of `ctx`.
   *
   * `ctx` is usually the current context, but the `context` of an obligation needs each
   * binder's type *in the preceding binders*, so there it is a prefix of the current one.
   * Binders the elaborator substitutes (a recursive function's parameters) are replaced by
   * their value; a binder that is missing entirely is an error, never a silent misread.
   */
  private fromExtractor(ctx: Ctx, term: Term, extDepth: number): Term {
    const args = new Map<number, Term>();
    for (const binder of ctx.binders) {
      const position = this.extOf.get(binder.id);
      if (position === undefined || position >= extDepth) continue;
      args.set(extDepth - 1 - position, K.varTerm(deBruijnIndex(ctx, binder)));
    }
    for (const [position, value] of this.inlineExt) {
      if (position >= extDepth) continue;
      const replacement = value(ctx);
      if (replacement !== undefined) args.set(extDepth - 1 - position, replacement);
    }
    try {
      return substituteFree(term, args);
    } catch (error) {
      throw new ElaborateFailure(
        `a term stored by the extractor (${K.formatTerm(term)}) mentions a binder this context does not have: ${
          error instanceof Error ? error.message : String(error)
        }`,
      );
    }
  }

  /**
   * A binder's type, as a term of `ctx`.  A type the extractor stored is renamed from the
   * extractor's layout; a type this module built (`ownType`: the state tuple, `px`, `ih`, the
   * invariant) is written in the context that was current when the binder was pushed, so it
   * only needs lifting past the later binders.
   */
  private binderTypeAt(ctx: Ctx, binder: Binder): Term {
    const at = ctx.binders.findIndex((candidate) => candidate.id === binder.id);
    // The binder in scope may be this module's own copy (the state tuple, `px`, `ih`, the
    // invariant); a fact still refers to the extractor's object.
    const bound = at < 0 ? binder : ctx.binders[at]!;
    if (!this.ownType.has(bound.id)) {
      const position = this.extOf.get(bound.id);
      if (position !== undefined) return this.fromExtractor(ctx, bound.type, position);
    }
    if (at < 0) return bound.type;
    return shiftTerm(bound.type, ctx.binders.length - at);
  }

  /** The proof of a site, weakened from the depth it was built at to `depth`. */
  private proofAt(siteId: number, depth: number): Term | undefined {
    const entry = this.proofs.get(siteId);
    if (entry === undefined) return undefined;
    if (entry.depth === depth) return entry.term;
    if (entry.depth > depth) {
      throw new ElaborateFailure(
        `the proof of obligation ${siteId} was built at depth ${entry.depth} and cannot be used at depth ${depth}`,
      );
    }
    return shiftTerm(entry.term, depth - entry.depth);
  }

  /** The proof of one of a recursive call's measure obligations, weakened to `depth`. */
  private selfCallProof(e: ExprIR, kind: ObligationKind, depth: number): Term {
    const site = e.sites.find((candidate) => candidate.kind === kind);
    if (site === undefined) throw new ElaborateFailure(`a recursive call has no \`${kind}\` obligation`);
    const proof = this.proofAt(site.id, depth);
    if (proof === undefined) {
      throw new ElaborateFailure(`the ${kind} obligation of this recursive call was not certified`);
    }
    return proof;
  }

  /** Record a site's proof, keeping the shallowest one (it can be weakened to any deeper use). */
  private storeProof(siteId: number, term: Term, depth: number): void {
    const existing = this.proofs.get(siteId);
    if (existing !== undefined && existing.depth <= depth) return;
    this.proofs.set(siteId, { term, depth });
    this.proofViews.clear();
  }

  /** The whole store, weakened to `depth` (what `exprTerm` reads for `index`/`slice`/`append`). */
  private proofsAt(depth: number): ReadonlyMap<number, Term> {
    const cached = this.proofViews.get(depth);
    if (cached !== undefined) return cached;
    const view = new Map<number, Term>();
    for (const [id, entry] of this.proofs) {
      view.set(id, entry.depth === depth ? entry.term : shiftTerm(entry.term, depth - entry.depth));
    }
    this.proofViews.set(depth, view);
    return view;
  }

  /** The next extractor position along the current path. */
  private nextExtDepth(ctx: Ctx): number {
    let max = -1;
    for (const binder of ctx.binders) {
      const position = this.extOf.get(binder.id);
      if (position !== undefined) max = Math.max(max, position);
    }
    // A binder that is *inlined* (a recursive function's parameter) still occupies its
    // extraction position, so the next extractor binder must be numbered after it.
    for (const position of this.inlineExt.keys()) max = Math.max(max, position);
    return max + 1;
  }

  /**
   * The binder an `ifLe` branch introduces.  Its domain is the *kernel's* (`Le a b` in the
   * yes branch, `Lt b a` in the no branch); the extractor's stored type renders the source
   * condition instead (`Eq a b`, `Not (Eq a b)`, …), and a hypothesis whose proof does not
   * have the proposition it is stated with makes `certify` reconstruct an equality row it
   * cannot prove.  The copy keeps the extractor's id, so slots still resolve.
   */
  private branchBinder(binder: Binder, type: Term): Binder {
    this.ownType.add(binder.id);
    return { ...binder, type };
  }

  /** Push an *extractor* binder: it takes the next extraction position. */
  private pushExt(ctx: Ctx, binder: Binder): Ctx {
    this.extOf.set(binder.id, this.nextExtDepth(ctx));
    return pushed(ctx, binder);
  }

  /** The `TermOptions` hooks this elaborator supplies (proofs, calls, inlined slots). */
  private get slotHooks(): Pick<TermOptions, "inlineSlots"> {
    return { inlineSlots: (ctx, slot) => this.inlineSlotTerm(ctx, slot) };
  }

  private inlineSlotTerm(ctx: Ctx, slot: Slot): Term | undefined {
    if (slot.kind !== "binder") return undefined;
    return this.inlineSlots.get(slot.binder.id)?.(ctx);
  }

  /**
   * The ambient binder types `certify` rebuilds its kernel context from: `types[p]` is the
   * type of the binder at position `p`, in the context of the *preceding* binders.  A type
   * the extractor stored is renamed from the extractor's layout; a type this module built is
   * already written in the context that was current when the binder was pushed.
   */
  private contextTypes(ctx: Ctx): Term[] {
    return ctx.binders.map((binder, position) => {
      const prefix: Ctx = { ...ctx, binders: ctx.binders.slice(0, position) };
      return this.binderTypeAt(prefix, binder);
    });
  }

  /** Atom names for counterexamples, with every loop-state projection named after its variable. */
  private atomNamesFor(ctx: Ctx): Record<string, string> {
    const depth = ctx.binders.length;
    const names = contextAtomNames(
      depth,
      ctx.binders.map((binder) => binder.surface ?? binder.name),
    );
    const values = Array.from({ length: depth }, (_, level) => K.vvar(level));
    for (const frame of this.loopStack) {
      const state = frame.loop.state;
      if (!ctx.binders.some((binder) => binder.id === state.id)) continue;
      const variable = K.varTerm(deBruijnIndex(ctx, state));
      for (const component of frame.components) {
        try {
          const value = K.evalTerm(this.env, project(variable, component.path), values);
          names[K.keyOfValue(value, K.irrelevantOf)] = component.name;
        } catch {
          // A component whose term cannot be evaluated simply keeps its positional name.
        }
      }
    }
    return names;
  }

  /**
   * `divFloorSpec`/`divTruncSpec*` for every division the obligation mentions.  The
   * extractor records the fact where the division *node* is, but a goal is often stated
   * about a `let`-bound local holding the quotient (`let mid = Math.floor((lo+hi)/2)`), and
   * a division by a constant is an opaque atom to Z3: the fact has to be stated about the
   * very term the goal mentions, which is what rebuilding it here guarantees.
   */
  private divisionFacts(ctx: Ctx, terms: readonly Term[], hyps: readonly Hyp[]): Hyp[] {
    const depth = ctx.binders.length;
    const out: Hyp[] = [];
    const seen = new Set<string>();
    const visit = (term: Term): void => {
      switch (term.tag) {
        case "Prim": {
          if (term.op === K.OP_DIV_FLOOR || term.op === K.OP_DIV_TRUNC) {
            const e = term.args[0];
            const k = term.args[1];
            if (e !== undefined && k !== undefined) {
              const key = `${term.op}|${K.formatTerm(term)}`;
              if (!seen.has(key)) {
                seen.add(key);
                const fact = this.divisionFactFor(term.op, e, k, hyps, depth);
                if (fact !== null) out.push(fact);
              }
            }
          }
          // Only the *value* arguments: a proof argument (the bounds proof of `get`, the
          // refutation of `byContra`, a whole `Farkas`) lives under binders of its own, so a
          // division found there would be stated about the wrong variables.
          const irrelevant = K.irrelevantOf(term.op) ?? [];
          term.args.forEach((arg, index) => {
            if (!irrelevant.includes(index)) visit(arg);
          });
          return;
        }
        case "Pi":
          visit(term.domain);
          visit(term.body);
          return;
        case "Sigma":
          visit(term.first);
          visit(term.second);
          return;
        case "App":
          visit(term.fn);
          visit(term.arg);
          return;
        default:
          return;
      }
    };
    for (const term of terms) visit(term);
    return out;
  }

  /** The lemma for one division: `divFloorSpec`, or a `divTruncSpec*` that needs a sign. */
  private divisionFactFor(
    op: K.PrimOp,
    e: Term,
    k: Term,
    hyps: readonly Hyp[],
    depth: number,
  ): Hyp | null {
    if (op === K.OP_DIV_FLOOR) {
      const fact = K.DivFloorSpec(e, k);
      return { term: fact, proof: fact, depth, origin: "division-spec" };
    }
    for (const hyp of hyps) {
      const at = hypAt(hyp, depth);
      if (sameTerm(at.term, K.Le(K.intLit(0n), e))) {
        const fact = K.DivTruncSpecNonneg(e, k, at.proof);
        return { term: fact, proof: fact, depth, origin: "division-spec" };
      }
      if (sameTerm(at.term, K.Lt(e, K.intLit(0n)))) {
        const fact = K.DivTruncSpecNeg(e, k, at.proof);
        return { term: fact, proof: fact, depth, origin: "division-spec" };
      }
    }
    return null;
  }

  /** Add the declaration the verdict allows, then report. */
  private finish(status: FunctionStatus, term?: Term): ElaborationOutcome {
    const result = this.snapshot(status, term);
    if (status === "certified") {
      const added = K.addDecl(this.env, {
        kind: "def",
        name: this.fn.name,
        type: this.fn.signature.type,
        value: term!,
      });
      if (added.ok) return { result, env: added.value };
      const diagnostic = this.declarationDiagnostic(
        `the kernel refused to declare \`${this.fn.name}\`: ${K.formatKernelError(added.error)}`,
      );
      return { result, env: this.env, declarationError: diagnostic };
    }
    // Not certified: admit the spec as an `external` declaration so callers can still be
    // elaborated; every caller is marked as depending on an uncertified function.
    const hash = this.options.sourceHash;
    if (this.options.admitUncertified === false) return { result, env: this.env };
    if (hash === undefined || hash === "") return { result, env: this.env };
    const added = K.addDecl(this.env, {
      kind: "external",
      name: this.fn.name,
      type: this.fn.signature.type,
      source: { file: this.fn.span.file, hash },
    });
    if (added.ok) return { result, env: added.value };
    return {
      result,
      env: this.env,
      declarationError: this.declarationDiagnostic(
        `the kernel refused the external declaration of \`${this.fn.name}\`: ${K.formatKernelError(added.error)}`,
      ),
    };
  }

  private snapshot(status: FunctionStatus, term?: Term): FunctionElaboration {
    return {
      name: this.fn.name,
      status,
      certified: status === "certified",
      term,
      type: this.fn.signature.type,
      obligations: [...this.outcomes.values()].sort((a, b) => a.siteId - b.siteId),
      diagnostics: sortDiagnostics(this.diagnostics),
      imports: this.fn.imports,
      dependsOnUncertified: [...this.dependsOnUncertified].sort(),
    };
  }

  // ---- diagnostics --------------------------------------------------------

  private internal(span: Span, message: string): void {
    this.diagnostics.push({ kind: "internal", severity: "error", span, message });
  }

  private declarationDiagnostic(message: string): Diagnostic {
    return { kind: "internal", severity: "error", span: this.fn.nameSpan, message };
  }

  // ---- hypotheses ---------------------------------------------------------

  /** The facts the signature itself supplies: parameters, vector bounds and preconditions. */
  private signatureHyps(ctx: Ctx): Hyp[] {
    const depth = ctx.binders.length;
    const out: Hyp[] = [];
    const index = (binder: Binder): number => deBruijnIndex(ctx, binder);

    for (const fact of this.fn.signature.preconditions) {
      const binder = fact.binder;
      if (binder === undefined) continue;
      let term: Term;
      try {
        term = exprTerm(ctx, fact.prop, this.optionsFor());
      } catch {
        term = shiftTerm(binder.type, 1);
      }
      out.push({ term, proof: K.varTerm(index(binder)), depth, prop: fact.prop, origin: "pre" });
    }

    for (let i = 0; i < ctx.binders.length; i += 1) {
      const proof = ctx.binders[i]!;
      if (proof.role !== "in-range") continue;
      const param = ctx.binders[i - 1];
      if (param === undefined || param.role !== "param") continue;
      if (param.type.tag !== "Prim" || param.type.op !== K.OP_INT) continue;
      out.push({
        term: K.InRange(K.varTerm(index(param))),
        proof: K.varTerm(index(proof)),
        depth,
        origin: "param-in-range",
      });
    }

    for (let i = 0; i < ctx.binders.length; i += 1) {
      const len = ctx.binders[i]!;
      if (len.role !== "vec-len") continue;
      const vec = ctx.binders[i + 1];
      if (vec === undefined || vec.role !== "param") continue;
      if (vec.type.tag !== "Prim" || vec.type.op !== K.OP_VEC) continue;
      const n = K.varTerm(index(len));
      const v = K.varTerm(index(vec));
      const vecType = this.binderTypeAt(ctx, vec);
      const elem = vecType.tag === "Prim" ? vecType.args[0]! : vec.type.args[0]!;
      out.push({
        term: K.And(K.Le(K.intLit(0n), n), K.Le(n, K.intLit(K.MAX_VEC_LEN))),
        proof: K.VecBounds(elem, n, v),
        depth,
        origin: "vec-bounds",
      });
    }
    return out;
  }

  /** The facts a site's own context recorded, rebuilt with proofs where possible. */
  private siteHyps(ctx: Ctx, site: ObligationSite, opts: TermOptions): Hyp[] {
    const depth = ctx.binders.length;
    const out: Hyp[] = [];
    for (const fact of site.hypotheses) {
      const hyp = this.factHyp(ctx, fact, opts, depth);
      if (hyp !== null) out.push(hyp);
    }
    return out;
  }

  private factHyp(ctx: Ctx, fact: FactIR, opts: TermOptions, depth: number): Hyp | null {
    if (fact.binder !== undefined) {
      // The binder's own type *is* the proposition its variable proves; using it keeps the
      // hypothesis and the proof in step even where the extractor's rendering differs (an
      // `if (a === b)` branch, for example, binds `Le a b`, not `Eq Int a b`).
      const binder = fact.binder;
      if (!this.inlineSlots.has(binder.id) && ctx.binders.some((candidate) => candidate.id === binder.id)) {
        return {
          term: this.binderTypeAt(ctx, binder),
          proof: K.varTerm(deBruijnIndex(ctx, binder)),
          depth,
          prop: fact.prop,
          origin: fact.origin,
        };
      }
      // The binder is *inlined* (a recursive function's parameter, replaced by a projection
      // of the argument tuple): restate the proposition from the IR and prove it with the
      // value the binder stands for.
      const proof = this.inlineSlots.get(binder.id)?.(ctx);
      if (proof === undefined) return null;
      try {
        return { term: exprTerm(ctx, fact.prop, opts), proof, depth, prop: fact.prop, origin: fact.origin };
      } catch {
        return null;
      }
    }
    switch (fact.origin) {
      case "vec-bounds":
        return this.vecBoundsHyp(ctx, fact, depth);
      case "element-range":
        return this.elementRangeHyp(ctx, fact, opts, depth);
      case "call-result":
        return this.callResultHyp(ctx, fact, opts, depth);
      case "field-in-range":
        return this.fieldRangeHyp(ctx, fact, opts, depth);
      default:
        return null;
    }
  }

  private vecBoundsHyp(ctx: Ctx, fact: FactIR, depth: number): Hyp | null {
    const lenRef = fact.prop.kind === "and" ? fact.prop.args[0]?.args[1] : undefined;
    const lenBinder = lenRef?.slot?.kind === "binder" ? lenRef.slot.binder : undefined;
    if (lenBinder === undefined) return null;
    const lenIndex = deBruijnIndex(ctx, lenBinder);
    for (const vec of ctx.binders) {
      if (vec.role !== "param" || vec.type.tag !== "Prim" || vec.type.op !== K.OP_VEC) continue;
      const vecType = this.binderTypeAt(ctx, vec);
      if (vecType.tag !== "Prim") continue;
      const second = vecType.args[1];
      if (second === undefined || second.tag !== "Var" || second.index !== lenIndex) continue;
      const n = K.varTerm(lenIndex);
      return {
        term: K.And(K.Le(K.intLit(0n), n), K.Le(n, K.intLit(K.MAX_VEC_LEN))),
        proof: K.VecBounds(vecType.args[0]!, n, K.varTerm(deBruijnIndex(ctx, vec))),
        depth,
        origin: "vec-bounds",
      };
    }
    return null;
  }

  /** `elems_a i p : InRange (get Int n_a a i p)` for a `readonly number[]` read. */
  private elementRangeHyp(ctx: Ctx, fact: FactIR, opts: TermOptions, depth: number): Hyp | null {
    const node = fact.prop.args[0];
    if (node === undefined || node.kind !== "index" || node.siteId === undefined) return null;
    const proof = this.proofAt(node.siteId, depth);
    if (proof === undefined) return null;
    const vec = node.args[0];
    const index = node.args[1];
    if (vec === undefined || index === undefined) return null;
    if (vec.kind !== "ref" || vec.slot?.kind !== "binder") return null;
    const name = vec.slot.binder.name;
    const elems = ctx.binders.find((b) => b.role === "vec-elems" && b.name === `elems_${name}`);
    if (elems === undefined) return null;
    try {
      return {
        term: exprTerm(ctx, fact.prop, opts),
        proof: K.app(K.app(K.varTerm(deBruijnIndex(ctx, elems)), exprTerm(ctx, index, opts)), proof),
        depth,
        origin: "element-range",
      };
    } catch {
      return null;
    }
  }

  private callResultHyp(ctx: Ctx, fact: FactIR, opts: TermOptions, depth: number): Hyp | null {
    const call = fact.prop.args[0];
    if (call === undefined || call.kind !== "call") return null;
    const path = call.layout?.inRangePath;
    if (path === undefined) return null;
    try {
      const packed = this.callTerm(ctx, call, opts);
      return { term: exprTerm(ctx, fact.prop, opts), proof: project(packed, path), depth, origin: "call-result" };
    } catch {
      return null;
    }
  }

  private fieldRangeHyp(ctx: Ctx, fact: FactIR, opts: TermOptions, depth: number): Hyp | null {
    const field = fact.prop.args[0];
    if (field === undefined || field.kind !== "field") return null;
    const path = field.field?.inRangePath;
    const slot = field.slot;
    if (path === undefined || slot === undefined) return null;
    try {
      const base = slot.kind === "payload" ? K.varTerm(deBruijnIndex(ctx, slot.payload)) : slotTerm(ctx, slot, opts);
      return { term: exprTerm(ctx, fact.prop, opts), proof: project(base, path), depth, origin: "field-in-range" };
    } catch {
      return null;
    }
  }

  /** `InRange` facts carried by every `number` field of a narrowed union payload. */
  private recordFacts(ctx: Ctx, binder: Binder, variant: VariantIR): Hyp[] {
    const out: Hyp[] = [];
    const base = K.varTerm(deBruijnIndex(ctx, binder));
    for (const field of variant.fields) {
      if (field.type.kind !== "int" || field.inRangePath === undefined) continue;
      out.push({
        term: K.InRange(project(base, field.path)),
        proof: project(base, field.inRangePath),
        depth: ctx.binders.length,
        origin: "field-in-range",
      });
    }
    return out;
  }

  // ---- options / override -------------------------------------------------

  private optionsFor(extra?: { result?: Term }): TermOptions {
    const base: TermOptions = {
      proofAt: (siteId, depth) => this.proofAt(siteId, depth),
      override: (ctx, e, opts) => this.overrideTerm(ctx, e, opts),
      inlineSlots: (ctx, slot) => this.inlineSlotTerm(ctx, slot),
    };
    return extra?.result === undefined ? base : { ...base, result: extra.result };
  }

  private withHyps<T>(hyps: readonly Hyp[], run: () => T): T {
    const saved = this.activeHyps;
    this.activeHyps = hyps;
    try {
      return run();
    } finally {
      this.activeHyps = saved;
    }
  }

  private overrideTerm(ctx: Ctx, e: ExprIR, opts: TermOptions): Term | undefined {
    if (e.kind === "call" && e.callee !== undefined && e.callee.kind !== "prelude") {
      return this.callTerm(ctx, e, opts);
    }
    if (e.kind === "append") return this.appendTerm(ctx, e, opts);
    return undefined;
  }

  // ---- calls --------------------------------------------------------------

  private signatureOf(callee: CalleeIR): SignatureIR | undefined {
    switch (callee.kind) {
      case "self":
        return this.fn.signature;
      case "imported":
        return callee.imported?.signature;
      case "local":
        return this.options.functions?.get(callee.name)?.signature;
      case "prelude":
        return undefined;
    }
  }

  /**
   * The packed application of a call, plus the argument term of every binder in the callee's
   * telescope (a `@post` of the callee is instantiated with them).  Memoised per call node so
   * that an auxiliary obligation is asked for at most once.
   */
  private callInfo(
    ctx: Ctx,
    e: ExprIR,
    opts: TermOptions,
  ): { depth: number; packed: Term; packedType?: Term; applied: Map<number, Term> } {
    const depth = ctx.binders.length;
    const bound = this.boundCalls.get(callSiteKey(e));
    if (bound !== undefined && bound.depth <= depth && ctx.binders.some((b) => b.id === bound.binder.id)) {
      const shift = depth - bound.depth;
      const applied = new Map<number, Term>();
      for (const [id, term] of bound.applied) applied.set(id, shiftTerm(term, shift));
      return {
        depth,
        packed: K.varTerm(deBruijnIndex(ctx, bound.binder)),
        packedType: shiftTerm(bound.binder.type, shift),
        applied,
      };
    }
    const cached = this.callCache.get(e);
    if (cached !== undefined && cached.depth === depth) return cached;
    const callee = e.callee;
    if (callee === undefined) throw new ElaborateFailure("a call expression without a callee");
    if (callee.kind === "prelude") {
      const built = callee.builtin!.build(e.args.map((arg) => exprTerm(ctx, arg, opts)));
      const info: { depth: number; packed: Term; packedType?: Term; applied: Map<number, Term> } = {
        depth,
        packed: built,
        applied: new Map<number, Term>(),
      };
      this.callCache.set(e, info);
      return info;
    }
    if (this.options.uncertified?.has(callee.name) === true) this.dependsOnUncertified.add(callee.name);
    const signature = this.signatureOf(callee);
    if (signature === undefined) {
      throw new ElaborateFailure(`no signature is available for the call to \`${callee.name}\``);
    }

    const params = signature.binders.filter((b) => b.role === "param");
    if (params.length !== e.args.length) {
      throw new ElaborateFailure(
        `\`${callee.name}\` takes ${params.length} argument(s) but the call has ${e.args.length}`,
      );
    }
    const paramInfo = new Map<number, { term: Term; expr: ExprIR }>();
    params.forEach((binder, i) => {
      const expr = e.args[i]!;
      paramInfo.set(binder.id, { term: exprTerm(ctx, expr, opts), expr });
    });

    const preProofs = this.preCallProofs(e, depth);
    const typeArgs = this.typeArguments(ctx, signature, e.args);
    const applied = new Map<number, Term>();
    const ordered: Term[] = [];
    /** The callee's non-type-parameter binders, in order: a recursive call's argument tuple. */
    const tupleValues: Term[] = [];
    let preIndex = 0;
    let previousParam: Binder | undefined;
    for (let i = 0; i < signature.binders.length; i += 1) {
      const binder = signature.binders[i]!;
      const push = (term: Term): void => {
        applied.set(binder.id, term);
        ordered.push(term);
        if (binder.role !== "type-param") tupleValues.push(term);
      };
      switch (binder.role) {
        case "type-param": {
          const argument = typeArgs.get(binder.id);
          if (argument === undefined) {
            throw new ElaborateFailure(`cannot infer the type argument \`${binder.surface ?? binder.name}\``);
          }
          push(argument);
          break;
        }
        case "param": {
          const info = paramInfo.get(binder.id);
          if (info === undefined) throw new ElaborateFailure(`missing argument for \`${binder.name}\``);
          push(info.term);
          previousParam = binder;
          break;
        }
        case "vec-len": {
          const next = signature.binders[i + 1];
          const info = next === undefined ? undefined : paramInfo.get(next.id);
          if (info?.expr.vecLength === undefined) {
            throw new ElaborateFailure(`the vector argument of \`${callee.name}\` has no length`);
          }
          push(exprTerm(ctx, info.expr.vecLength, opts));
          break;
        }
        case "in-range": {
          const info = previousParam === undefined ? undefined : paramInfo.get(previousParam.id);
          if (info === undefined) throw new ElaborateFailure("an `InRange` proof has no parameter");
          push(this.inRangeProof(ctx, info.expr, info.term));
          break;
        }
        case "vec-elems": {
          const info = previousParam === undefined ? undefined : paramInfo.get(previousParam.id);
          if (info === undefined) throw new ElaborateFailure("an element proof has no parameter");
          push(this.elemsProof(ctx, info.expr, opts, callee.name));
          break;
        }
        case "pre": {
          const proof = preProofs[preIndex];
          preIndex += 1;
          if (proof === undefined) {
            throw new ElaborateFailure(`no certified proof for a precondition of \`${callee.name}\``);
          }
          push(proof);
          break;
        }
        default:
          throw new ElaborateFailure(`unsupported binder role \`${binder.role}\` in \`${callee.name}\``);
      }
    }
    // A recursive call is an application of the induction hypothesis to the new argument
    // tuple, the two measure proofs and the callee's preconditions — the *callee* is `ih`.
    let packed: Term;
    if (callee.kind === "self") {
      const frame = this.recursion;
      if (frame === null) throw new ElaborateFailure("a recursive call outside a recursive function");
      const state = this.packTuple(frame.spec, ctx, tupleValues);
      const nonneg = this.selfCallProof(e, "measure-nonneg", depth);
      const decrease = this.selfCallProof(e, "measure-decrease", depth);
      packed = K.appMany(K.varTerm(deBruijnIndex(ctx, frame.ih)), [state, nonneg, decrease, ...preProofs]);
    } else {
      packed = K.appMany(K.constTerm(callee.name), ordered);
    }
    const info: { depth: number; packed: Term; packedType?: Term; applied: Map<number, Term> } = {
      depth,
      packed,
      applied,
    };
    try {
      info.packedType = substituteFree(signature.result.term, this.calleeArguments(signature, applied));
    } catch {
      // the packed type is only needed to annotate a `let`; a failure here is not fatal
    }
    this.callCache.set(e, info);
    return info;
  }

  private callTerm(ctx: Ctx, e: ExprIR, opts: TermOptions): Term {
    return this.callInfo(ctx, e, opts).packed;
  }

  /**
   * The callee's `@post` facts at the call site: the packed result's `postPath` holds the
   * `And`-conjunction of their proofs, and the propositions are instantiated with the call's
   * arguments and the call's result value.
   */
  private callPostHyps(
    ctx: Ctx,
    e: ExprIR,
    info: { packed: Term; applied: Map<number, Term> },
    opts: TermOptions,
  ): Hyp[] {
    const callee = e.callee;
    const layout = e.layout;
    if (callee === undefined || callee.kind === "prelude" || layout?.postPath === undefined) return [];
    const signature = this.signatureOf(callee);
    if (signature === undefined || signature.result.posts.length === 0) return [];
    const depth = ctx.binders.length;
    const conjunction = project(info.packed, layout.postPath);
    const resultTerm = project(
      info.packed,
      layout.shape === "vec" ? layout.lengthPath ?? [0] : layout.valuePath,
    );
    const out: Hyp[] = [];
    for (let i = 0; i < signature.result.posts.length; i += 1) {
      const prop = signature.result.posts[i]!.prop;
      let term: Term;
      try {
        term = this.instantiateCalleePost(signature, info, prop, resultTerm, opts);
      } catch {
        continue; // a postcondition this call site cannot express is simply not assumed
      }
      out.push({
        term,
        proof: project(conjunction, conjunctionProjection(i, signature.result.posts.length)),
        depth,
        origin: "call-result",
      });
    }
    return out;
  }

  /** A callee `@post` in the callee's own context, with its binders substituted by the call. */
  private instantiateCalleePost(
    signature: SignatureIR,
    info: { applied: Map<number, Term> },
    prop: ExprIR,
    resultTerm: Term,
    opts: TermOptions,
  ): Term {
    const resultBinder = signature.result.binder;
    const binders =
      resultBinder === undefined ? [...signature.binders] : [...signature.binders, resultBinder];
    const calleeCtx: Ctx = { binders, facts: [], narrowings: [], ids: new Ids() };
    const term = exprTerm(calleeCtx, prop, { ...opts, result: K.varTerm(0) });
    const args = this.calleeArguments(signature, info.applied, binders.length);
    if (resultBinder !== undefined) args.set(0, resultTerm);
    return substituteFree(term, args);
  }

  /**
   * The callee's signature binders as free de Bruijn indices of one of its own contexts,
   * mapped to the call's arguments.  `depth` is the depth of that context (the signature
   * telescope alone, or the telescope plus the result binder for the codomain), so the
   * binder at `position` sits at index `depth - 1 - position`.
   */
  private calleeArguments(
    signature: SignatureIR,
    applied: ReadonlyMap<number, Term>,
    depth: number = signature.binders.length,
  ): Map<number, Term> {
    const args = new Map<number, Term>();
    signature.binders.forEach((binder, position) => {
      const value = applied.get(binder.id);
      if (value === undefined) return;
      args.set(depth - 1 - position, value);
    });
    return args;
  }

  /** The pre-call site's proof, split into one proof per precondition binder. */
  private preCallProofs(e: ExprIR, depth: number): Term[] {
    const callee = e.callee;
    const count = callee === undefined || callee.kind === "prelude" ? 0 : (this.signatureOf(callee)?.preconditions.length ?? 0);
    const site = e.sites.find((s) => s.kind === "pre-call");
    if (site === undefined) {
      if (count === 0) return [];
      throw new ElaborateFailure("the call has preconditions but no pre-call obligation");
    }
    const proof = this.proofAt(site.id, depth);
    if (proof === undefined) throw new ElaborateFailure("the pre-call obligation of this call was not certified");
    const out: Term[] = [];
    for (let i = 0; i < count; i += 1) {
      const path = conjunctionProjection(i, count);
      out.push(path.length === 0 ? proof : project(proof, path));
    }
    return out;
  }

  /** Inferred type arguments for a generic callee, from the call's argument types. */
  private typeArguments(ctx: Ctx, signature: SignatureIR, args: readonly ExprIR[]): Map<number, Term> {
    const out = new Map<number, Term>();
    for (const binder of signature.binders) {
      if (binder.role !== "type-param") continue;
      const name = binder.surface ?? binder.name;
      for (const arg of args) {
        const term = this.typeArgumentFor(ctx, arg.type, name);
        if (term !== undefined) {
          out.set(binder.id, term);
          break;
        }
      }
    }
    return out;
  }

  private typeArgumentFor(ctx: Ctx, type: TypeIR, name: string): Term | undefined {
    switch (type.kind) {
      case "generic":
        return type.typeParam === name ? this.resolvedTypeParam(ctx, name) : undefined;
      case "vec":
        return this.typeArgumentFor(ctx, type.elem!, name);
      default:
        return undefined;
    }
  }

  private resolvedTypeParam(ctx: Ctx, name: string): Term {
    for (let i = ctx.binders.length - 1; i >= 0; i -= 1) {
      const binder = ctx.binders[i]!;
      if (binder.role === "type-param" && (binder.surface ?? binder.name) === name) {
        return K.varTerm(deBruijnIndex(ctx, binder));
      }
    }
    throw new ElaborateFailure(`the type parameter \`${name}\` is not in scope`);
  }

  private inRangeProof(ctx: Ctx, expr: ExprIR, term: Term): Term {
    const depth = ctx.binders.length;
    if (expr.kind === "int") return this.literalInRange(expr.literal as bigint);
    // A fact already in scope (a parameter's proof binder, a range site, a call result, …).
    const wanted = K.InRange(term);
    for (const hyp of hypsAt(this.activeHyps, depth)) {
      if (sameTerm(hyp.term, wanted)) return hyp.proof;
    }
    const proof = this.proveAux(
      ctx,
      this.activeHyps,
      wanted,
      "range",
      expr.span,
      "the range of a call argument",
    );
    if (proof === undefined) throw new ElaborateFailure("cannot prove that this call argument is in range");
    return proof;
  }

  private literalInRange(value: bigint): Term {
    if (value < -K.SAFE_MAX || value > K.SAFE_MAX) {
      throw new ElaborateFailure(`the literal ${value} is outside the safe integer range`);
    }
    return K.pair(K.InRange(K.intLit(value)), K.LeProof(-K.SAFE_MAX, value), K.LeProof(value, K.SAFE_MAX));
  }

  /**
   * `(i : Int) -> (p : And (Le 0 i) (Lt i n)) -> InRange (get …)`: the element-boundary
   * proof a `readonly number[]` argument needs.  Only a caller that received the same vector
   * as a `readonly number[]` parameter can supply it — that parameter's own guard is the
   * proof.
   */
  private elemsProof(ctx: Ctx, expr: ExprIR, opts: TermOptions, calleeName: string): Term {
    if (expr.kind !== "ref" || expr.slot?.kind !== "binder") {
      throw new ElaborateFailure(
        `cannot build the element-boundary proof for the \`readonly number[]\` argument of \`${calleeName}\``,
      );
    }
    const binder = expr.slot.binder;
    const elems = ctx.binders.find((b) => b.role === "vec-elems" && b.name === `elems_${binder.name}`);
    if (elems === undefined) {
      throw new ElaborateFailure(
        `\`${binder.surface ?? binder.name}\` is not a \`readonly number[]\` parameter of the caller, so the ` +
          `element-boundary proof for \`${calleeName}\` cannot be built`,
      );
    }
    if (expr.vecLength === undefined) throw new ElaborateFailure("the vector argument has no length");
    const n = exprTerm(ctx, expr.vecLength, opts);
    const iBinder: Binder = { id: freshId(), name: "i", role: "local", type: K.Int };
    const iCtx = pushed(ctx, iBinder);
    const boundsType = K.And(
      K.Le(K.intLit(0n), K.varTerm(0)),
      K.Lt(K.varTerm(0), shiftTerm(n, 1)),
    );
    const pBinder: Binder = { id: freshId(), name: "p", role: "hypothesis", type: boundsType };
    const pCtx = pushed(iCtx, pBinder);
    const body = K.app(
      K.app(K.varTerm(deBruijnIndex(pCtx, elems)), K.varTerm(deBruijnIndex(pCtx, iBinder))),
      K.varTerm(deBruijnIndex(pCtx, pBinder)),
    );
    return K.lam("i", K.Int, K.lam("p", boundsType, body));
  }

  // ---- append -------------------------------------------------------------

  private appendTerm(ctx: Ctx, e: ExprIR, opts: TermOptions): Term {
    const elem = this.elemType(ctx, e.type.elem!);
    const site = e.sites.find((s) => s.kind === "append-length");
    const siteProof = site === undefined ? undefined : this.proofAt(site.id, ctx.binders.length);
    if (siteProof === undefined) throw new ElaborateFailure("the append-length obligation was not certified");

    const parts = e.args;
    const lengths = parts.map((part) => {
      if (part.vecLength === undefined) throw new ElaborateFailure("a spread part has no length");
      return exprTerm(ctx, part.vecLength, opts);
    });
    const total = lengths.reduce((a, b) => K.Add(a, b), K.intLit(0n));
    if (parts.length === 0) throw new ElaborateFailure("an array literal needs at least one spread part");

    // `[...p0, …]` is `p0` when there is a single part, and an `append` chain otherwise —
    // there is no empty vector value in the kernel, so the first part is the seed.
    let length: Term = lengths[0]!;
    let vec: Term = exprTerm(ctx, parts[0]!, opts);
    for (let i = 1; i < parts.length; i += 1) {
      const partLen = lengths[i]!;
      const needed = K.Le(K.Add(length, partLen), K.intLit(K.MAX_VEC_LEN));
      let proof = siteProof;
      if (i < parts.length - 1) {
        // The site's proof is about the whole concatenation; an intermediate prefix needs
        // its own derivation from it (`Le (prefix + part) MAX`).
        const derived = this.proveAux(
          ctx,
          [
            ...this.activeHyps,
            {
              term: K.Le(total, K.intLit(K.MAX_VEC_LEN)),
              proof: siteProof,
              depth: ctx.binders.length,
              origin: "append-length",
            },
          ],
          needed,
          "append-length",
          e.span,
          "an intermediate array spread length",
        );
        if (derived === undefined) throw new ElaborateFailure("an intermediate spread length is out of bounds");
        proof = derived;
      }
      vec = K.Append(elem, length, partLen, vec, exprTerm(ctx, parts[i]!, opts), proof);
      length = K.Add(length, partLen);
    }
    return vec;
  }

  private elemType(ctx: Ctx, type: TypeIR): Term {
    switch (type.kind) {
      case "int":
        return K.Int;
      case "union":
        return type.union!.sumType;
      case "generic":
        return this.resolvedTypeParam(ctx, type.typeParam!);
      default:
        throw new ElaborateFailure("a nested vector is not in the fragment");
    }
  }

  // ---- sites --------------------------------------------------------------

  /** Certify every site attached to `e` and its children, in this context. */
  private prepare(ctx: Ctx, hyps: readonly Hyp[], e: ExprIR, opts: TermOptions): Hyp[] {
    const depth = ctx.binders.length;
    const facts: Hyp[] = [];
    const base = (): Hyp[] => [...hyps, ...facts];

    if (e.kind === "cond" && e.cond !== undefined) {
      this.prepareCond(ctx, base(), e.cond, opts);
    } else {
      for (const arg of e.args) facts.push(...this.prepare(ctx, base(), arg, opts));
      if (e.vecLength !== undefined) facts.push(...this.prepare(ctx, base(), e.vecLength, opts));
    }

    this.withHyps(base(), () => this.certifySites(ctx, base(), e.sites, opts));
    facts.push(...this.derivedFacts(ctx, e, base(), opts));

    // Only facts valid at this depth survive; facts from inside a branch do not.
    return facts.filter((fact) => fact.depth === depth);
  }

  private prepareCond(ctx: Ctx, hyps: readonly Hyp[], cond: CondIR, opts: TermOptions): void {
    const depth = ctx.binders.length;
    const conditionFacts = this.prepare(ctx, hyps, cond.expr, opts);
    const base = [...hyps, ...conditionFacts];

    if (cond.tagTest !== undefined) {
      const union = cond.tagTest.union;
      const thenVariant = cond.thenNarrowings[0]?.variant ?? otherVariant(union, cond.tagTest.variant);
      const elseVariant = cond.elseNarrowings[0]?.variant ?? cond.tagTest.variant;
      const thenCtx = this.pushExt(ctx, cond.thenBinder);
      const elseCtx = this.pushExt(ctx, cond.elseBinder);
      if (cond.thenExpr !== undefined) {
        this.prepare(
          thenCtx,
          [...hypsAt(base, depth + 1), ...this.recordFacts(thenCtx, cond.thenBinder, thenVariant)],
          cond.thenExpr,
          opts,
        );
      }
      if (cond.elseExpr !== undefined) {
        this.prepare(
          elseCtx,
          [...hypsAt(base, depth + 1), ...this.recordFacts(elseCtx, cond.elseBinder, elseVariant)],
          cond.elseExpr,
          opts,
        );
      }
      return;
    }

    const [a, b] = this.ifLeOperands(ctx, cond.expr, opts);
    const thenBinder = this.branchBinder(cond.thenBinder, K.Le(a, b));
    const elseBinder = this.branchBinder(cond.elseBinder, K.Lt(b, a));
    const thenCtx = this.pushExt(ctx, thenBinder);
    const elseCtx = this.pushExt(ctx, elseBinder);
    if (cond.thenExpr !== undefined) {
      this.prepare(
        thenCtx,
        [
          ...hypsAt(base, depth + 1),
          { term: shiftTerm(K.Le(a, b), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
        ],
        cond.thenExpr,
        opts,
      );
    }
    if (cond.elseExpr !== undefined) {
      this.prepare(
        elseCtx,
        [
          ...hypsAt(base, depth + 1),
          { term: shiftTerm(K.Lt(b, a), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
        ],
        cond.elseExpr,
        opts,
      );
    }
  }

  /** Facts a node itself justifies: its range site, a call result, an element guard. */
  private derivedFacts(ctx: Ctx, e: ExprIR, hyps: readonly Hyp[], opts: TermOptions): Hyp[] {
    const depth = ctx.binders.length;
    const out: Hyp[] = [];
    for (const site of e.sites) {
      if (site.kind !== "range") continue;
      const proof = this.proofAt(site.id, depth);
      if (proof === undefined) continue;
      try {
        out.push({ term: exprTerm(ctx, site.goal, opts), proof, depth, origin: "range" });
      } catch {
        // The goal cannot be built without a proof we do not have; the site's own
        // certification has reported it.
      }
    }
    for (const fact of e.facts) {
      const hyp = this.factHyp(ctx, fact, opts, depth);
      if (hyp !== null) out.push(hyp);
    }
    if (e.kind === "call" && e.callee?.kind !== "prelude" && e.callee !== undefined) {
      try {
        const info = this.callInfo(ctx, e, opts);
        out.push(...this.callPostHyps(ctx, e, info, opts));
      } catch {
        // the call cannot be built; its own diagnostics are reported elsewhere
      }
    }
    if (e.kind === "call" && e.callee?.kind === "prelude" && e.callee.builtin?.division === true) {
      const spec = this.divisionSpec(ctx, e, hyps, opts);
      if (spec !== null) out.push(spec);
    }
    return out;
  }

  /** `divFloorSpec`/`divTruncSpec*`: what makes a constant-divisor division usable. */
  private divisionSpec(ctx: Ctx, e: ExprIR, hyps: readonly Hyp[], opts: TermOptions): Hyp | null {
    const builtin = e.callee?.builtin;
    const numerator = e.args[0];
    const divisor = e.args[1];
    if (builtin === undefined || numerator === undefined || divisor === undefined) return null;
    const depth = ctx.binders.length;
    try {
      const n = exprTerm(ctx, numerator, opts);
      const k = exprTerm(ctx, divisor, opts);
      if (builtin.kind === "floor") {
        return { term: K.DivFloorSpec(n, k), proof: K.DivFloorSpec(n, k), depth, origin: "division-spec" };
      }
      if (builtin.kind === "trunc") {
        for (const hyp of [...hypsAt(hyps, depth), ...hypsAt(this.activeHyps, depth)]) {
          if (sameTerm(hyp.term, K.Le(K.intLit(0n), n))) {
            return {
              term: K.DivTruncSpecNonneg(n, k, hyp.proof),
              proof: K.DivTruncSpecNonneg(n, k, hyp.proof),
              depth,
              origin: "division-spec",
            };
          }
          if (sameTerm(hyp.term, K.Lt(n, K.intLit(0n)))) {
            return {
              term: K.DivTruncSpecNeg(n, k, hyp.proof),
              proof: K.DivTruncSpecNeg(n, k, hyp.proof),
              depth,
              origin: "division-spec",
            };
          }
        }
      }
    } catch {
      return null;
    }
    return null;
  }

  private certifySites(ctx: Ctx, hyps: readonly Hyp[], sites: readonly ObligationSite[], opts: TermOptions): void {
    for (const site of sites) this.certifySite(ctx, hyps, site, opts);
  }

  private certifySite(
    ctx: Ctx,
    hyps: readonly Hyp[],
    site: ObligationSite,
    opts: TermOptions,
    result?: Term,
  ): boolean {
    if (this.visited.has(site.id)) return this.outcomes.get(site.id)?.status === "certified";
    this.visited.add(site.id);
    const solved = this.solve(ctx, hyps, site, opts, result);
    this.storeProof(site.id, solved.proof ?? K.tt, ctx.binders.length);
    this.record(site, solved.status, solved.detail);
    if (solved.status === "certified") return true;
    this.reportFailure(site, solved);
    return false;
  }

  /**
   * A `@post` on a return whose value is a ternary: the packing is pushed into the
   * conditional, so the same site is solved once per branch, each in its own context (with
   * that branch's hypothesis).  The site is certified only when *every* branch is.
   */
  private certifyPost(ctx: Ctx, hyps: readonly Hyp[], site: ObligationSite, value: Term): Term {
    this.visited.add(site.id);
    const solved = this.solve(ctx, hyps, site, this.optionsFor(), value);
    const previous = this.outcomes.get(site.id);
    if (previous === undefined || previous.status === "certified" || solved.status !== "certified") {
      this.record(site, solved.status, solved.detail);
    }
    if (solved.status !== "certified") this.reportFailure(site, solved);
    return solved.proof ?? K.tt;
  }

  /** Build one obligation, fill it, and report what happened (no bookkeeping). */
  private solve(
    ctx: Ctx,
    hyps: readonly Hyp[],
    site: ObligationSite,
    opts: TermOptions,
    result?: Term,
  ): { status: ObligationStatus; proof?: Term; detail?: SolveDetail } {
    const depth = ctx.binders.length;
    let goal: Term;
    let hypotheses: Hyp[];
    try {
      goal = exprTerm(ctx, site.goal, result === undefined ? opts : { ...opts, result });
      const base = [...hypsAt(hyps, depth), ...this.siteHyps(ctx, site, opts)];
      hypotheses = expandEquations(
        dedupeHyps([
          ...base,
          // A division by a constant is an opaque atom to Z3: the lemma has to be stated
          // about the very terms the goal and the hypotheses mention.
          ...this.divisionFacts(ctx, [goal, ...base.map((hyp) => hyp.term)], base),
        ]),
      );
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      this.internal(site.span, `the ${site.kind} obligation of \`${this.fn.name}\` cannot be built: ${detail}`);
      return { status: "failed", detail: { reason: `the obligation cannot be built: ${detail}` } };
    }

    // A hole whose goal is literally a hypothesis in scope needs no solver.
    for (const hyp of hypotheses) {
      if (sameTerm(hyp.term, goal)) {
        return { status: "certified", proof: hyp.proof, detail: { reason: "the goal is a hypothesis in scope" } };
      }
    }

    // No solver: the obligation is not discharged, and lenient mode injects a runtime check.
    if (this.options.solver === false) {
      this.noSolver = true;
      return { status: "smt-only", detail: { reason: NO_SOLVER_REASON } };
    }

    const kept = hypotheses;
    const obligation: Obligation = {
      id: `${this.fn.name}#${site.id}`,
      kind: site.kind,
      span: site.span,
      context: this.contextTypes(ctx),
      hypotheses: kept.map((hyp) => hyp.term),
      proofs: kept.map((hyp) => hyp.proof),
      goal,
      atomNames: this.atomNamesFor(ctx),
    };

    const outcome = this.withHyps(hypotheses, () =>
      certify(this.env, obligation, { timeoutMs: this.options.timeoutMs }),
    );

    if (outcome.status === "certified" && outcome.proof !== undefined) {
      return { status: "certified", proof: outcome.proof };
    }
    const detail: SolveDetail = {
      ...(outcome.reason === undefined ? {} : { reason: outcome.reason }),
      ...(outcome.path === undefined ? {} : { path: [...outcome.path] }),
      ...(outcome.counterexample === undefined ? {} : { counterexample: outcome.counterexample }),
    };
    return { status: outcome.status === "smt-only" ? "smt-only" : "failed", detail };
  }

  private reportFailure(
    site: ObligationSite,
    solved: { status: ObligationStatus; detail?: SolveDetail },
  ): void {
    if (solved.status === "smt-only") {
      this.diagnostics.push({
        kind: "uncertified",
        severity: "warning",
        span: site.span,
        message:
          solved.detail?.reason === NO_SOLVER_REASON
            ? `no SMT solver is available, so the ${site.kind} obligation \`${site.text}\` was ` +
              `not discharged; a runtime check will be needed`
            : `Z3 proved the ${site.kind} obligation \`${site.text}\` but no kernel certificate was ` +
              `found; a runtime check will be needed`,
      });
      return;
    }
    this.diagnostics.push({
      kind: site.kind,
      severity: "error",
      span: site.span,
      message:
        solved.detail?.counterexample === undefined
          ? `${obligationMessage(site.kind, site.text)}${solved.detail?.reason === undefined ? "" : ` (${solved.detail.reason})`}`
          : obligationMessage(site.kind, site.text),
      ...(solved.detail?.path === undefined ? {} : { path: [...solved.detail.path] }),
      ...(solved.detail?.counterexample === undefined ? {} : { counterexample: solved.detail.counterexample }),
    });
  }

  private record(site: ObligationSite, status: ObligationStatus, detail?: SolveDetail): void {
    this.outcomes.set(site.id, {
      siteId: site.id,
      kind: site.kind,
      span: site.span,
      text: site.text,
      status,
      ...(detail?.reason === undefined ? {} : { reason: detail.reason }),
      ...(detail?.path === undefined ? {} : { path: detail.path }),
      ...(detail?.counterexample === undefined ? {} : { counterexample: detail.counterexample }),
    });
  }

  /** Certify a derived obligation that has no source site (an intermediate spread length). */
  private proveAux(
    ctx: Ctx,
    hyps: readonly Hyp[],
    goal: Term,
    kind: ObligationKind,
    span: Span,
    what: string,
  ): Term | undefined {
    const depth = ctx.binders.length;
    const base = hypsAt(hyps, depth);
    const list = expandEquations(
      dedupeHyps([...base, ...this.divisionFacts(ctx, [goal, ...base.map((hyp) => hyp.term)], base)]),
    );
    for (const hyp of list) {
      if (sameTerm(hyp.term, goal)) return hyp.proof;
    }
    // No solver: leave a placeholder proof and a warning.  `noSolver` keeps the function from
    // being certified, so the kernel never sees the placeholder.
    if (this.options.solver === false) {
      this.noSolver = true;
      this.diagnostics.push({
        kind: "uncertified",
        severity: "warning",
        span,
        message: `no SMT solver is available, so ${what} was not discharged; a runtime check will be needed`,
      });
      return K.tt;
    }
    this.auxCount += 1;
    const obligation: Obligation = {
      id: `${this.fn.name}#aux${this.auxCount}`,
      kind,
      span,
      context: this.contextTypes(ctx),
      hypotheses: list.map((hyp) => hyp.term),
      proofs: list.map((hyp) => hyp.proof),
      goal,
      atomNames: this.atomNamesFor(ctx),
    };
    const outcome = certify(this.env, obligation, { timeoutMs: this.options.timeoutMs });
    if (outcome.status === "certified" && outcome.proof !== undefined) return outcome.proof;
    this.diagnostics.push({
      kind,
      severity: "error",
      span,
      message:
        `${what} cannot be certified${outcome.reason === undefined ? "" : `: ${outcome.reason}`}` +
        (outcome.counterexample === undefined
          ? ""
          : `; counterexample: ${Object.entries(outcome.counterexample)
              .map(([name, value]) => `${name} = ${value}`)
              .join(", ")}`),
    });
    return undefined;
  }

  /** Certify any site the walk never reached, so every site has a verdict. */
  private sweep(ctx: Ctx, hyps: readonly Hyp[]): void {
    const opts = this.optionsFor();
    for (const site of this.fn.sites) {
      if (this.visited.has(site.id)) continue;
      this.certifySite(ctx, hyps, site, opts);
    }
  }

  // ---- loops --------------------------------------------------------------

  /**
   * A `LoopIR` as `fixWf A B m step s0 p0 hinv0 : Result` (specification 6.3):
   *
   * ```text
   * A    = Sigma (v0 : T0). … Unit            -- the carried-state tuple
   * B    = fun (_ : A) => Inv s -> Result
   * m    = fun (s : A) => <@decreases>
   * step = fun (s : A) (px : Le 0 (m s)) (ih : (y : A) -> Le 0 (m y) -> Lt (m y) (m s) -> B y)
   *            (hinv : Inv s) => if cond then body else rest
   * ```
   *
   * `A`, `B` and `m` are rebuilt from the IR rather than taken from `LoopIR`'s stored terms:
   * those are written in the *enclosing* context, and a loop nested in another loop would
   * read them at the wrong depth.  `rest` — the statements after the loop — is the `else`
   * branch, so the loop term *is* the rest of the function.  `continue` becomes an
   * application of `ih` to the new state and the three back-edge proofs.
   */
  private elabLoop(ctx: Ctx, hyps: readonly Hyp[], loop: LoopIR): Term {
    const opts = this.optionsFor();
    const depth = ctx.binders.length;

    const spec = this.loopSpec(ctx, loop);
    const stateType = this.tupleType(spec, ctx);
    const state: Binder = { ...loop.state, type: stateType };
    this.ownType.add(state.id);
    const stateCtx = this.pushExt(ctx, state);
    const stateHyps = hypsAt(hyps, depth + 1);
    const invariantTerm = this.withHyps(stateHyps, () => exprTerm(stateCtx, loop.invariant, opts));
    const measureFn = K.lam("s", stateType, this.withHyps(stateHyps, () => exprTerm(stateCtx, loop.measure, opts)));
    const resultType = this.resultTypeAt(ctx);

    // `px : Le 0 (m s)`, bound under the state, then `ih`, then the invariant.
    const pxType = K.Le(K.intLit(0n), K.app(shiftTerm(measureFn, 1), K.varTerm(0)));
    const px: Binder = { id: freshId(), name: "px", role: "loop-measure-nonneg", type: pxType };
    this.ownType.add(px.id);
    const measureCtx = this.pushExt(stateCtx, px);

    const stateVar = K.varTerm(1); // `s` in `measureCtx`
    // `B = fun _ => Inv s -> Result`, and `ih`'s type; both are terms of `measureCtx`, so the
    // domain `A` and the functions `m`/`B` (which live in the enclosing context) are shifted
    // by the two binders `s` and `px` that were pushed since.
    const predicate: Term = K.lam(
      "_",
      stateType,
      K.pi("hinv", invariantTerm, shiftTerm(resultType, 2)),
    );
    const ihType = K.pi(
      "y",
      shiftTerm(stateType, 2),
      K.pi(
        "py",
        K.Le(K.intLit(0n), K.app(shiftTerm(measureFn, 3), K.varTerm(0))),
        K.pi(
          "pd",
          K.Lt(
            K.app(shiftTerm(measureFn, 4), K.varTerm(1)),
            K.app(shiftTerm(measureFn, 4), shiftTerm(stateVar, 2)),
          ),
          K.app(shiftTerm(predicate, 5), K.varTerm(2)),
        ),
      ),
    );
    const ih: Binder = { id: freshId(), name: "ih", role: "local", type: ihType };
    const ihCtx = pushed(measureCtx, ih);

    const hinv: Binder = { ...loop.invariantBinder, type: shiftTerm(invariantTerm, 2) };
    this.ownType.add(hinv.id);
    const bodyCtx = this.pushExt(ihCtx, hinv);
    const bodyDepth = bodyCtx.binders.length;

    const frame: LoopContext = {
      loop,
      ih,
      measure: measureFn,
      invariant: predicate,
      components: spec.components,
      spec,
      stateDepth: depth,
    };
    this.loopStack.push(frame);
    let body: Term;
    try {
      body = this.elabIf(bodyCtx, this.loopHyps(bodyCtx, hyps, px, hinv), {
        kind: "if",
        cond: loop.test,
        then: loop.body,
        otherwise: loop.rest,
        span: loop.span,
      });
    } finally {
      this.loopStack.pop();
    }

    const step = K.lam(
      "s",
      stateType,
      K.lam(
        "px",
        pxType,
        K.lam("ih", ihType, K.lam(hinv.name, hinv.type, body)),
      ),
    );

    // The init obligations (in the enclosing context) become `p0` and `hinv0`.
    this.withHyps(hyps, () => this.certifySites(ctx, hyps, loop.initSites, opts));
    const initial = loop.carried.map((carried) => exprTerm(ctx, carried.initial, opts));
    const start = this.packTuple(spec, ctx, initial);
    const nonneg = loop.initSites.find((site) => site.kind === "measure-nonneg");
    const init = loop.initSites.find((site) => site.kind === "invariant-init");
    const p0 = nonneg === undefined ? K.tt : this.proofAt(nonneg.id, depth) ?? K.tt;
    const hinv0 = init === undefined ? K.tt : this.proofAt(init.id, depth) ?? K.tt;

    const loopTerm = K.FixWf(0, stateType, predicate, measureFn, step, start, p0);
    void bodyDepth;
    return K.app(loopTerm, hinv0);
  }

  /** The hypotheses available in a loop body: the signature's, plus `px` and `hinv`. */
  private loopHyps(ctx: Ctx, hyps: readonly Hyp[], px: Binder, hinv: Binder): Hyp[] {
    const depth = ctx.binders.length;
    return dedupeHyps([
      ...hypsAt(hyps, depth),
      ...this.signatureHyps(ctx),
      {
        term: this.binderTypeAt(ctx, px),
        proof: K.varTerm(deBruijnIndex(ctx, px)),
        depth,
        origin: "measure",
      },
      {
        term: this.binderTypeAt(ctx, hinv),
        proof: K.varTerm(deBruijnIndex(ctx, hinv)),
        depth,
        origin: "invariant",
      },
    ]);
  }

  /** The carried-state components: name, kernel type and tuple path. */
  private loopSpec(ctx: Ctx, loop: LoopIR): TupleSpec {
    const components: Component[] = loop.carried.map((carried, index) => ({
      name: carried.name,
      type: this.valueType(ctx, carried.type),
      path: componentPath(index),
    }));
    const typeDepth = ctx.binders.length;
    return {
      components,
      typeAt: (at, bound, index) =>
        shiftTerm(components[index]!.type, bound + (at.binders.length - typeDepth)),
    };
  }

  /** The kernel type of a value of `type`, in `ctx`. */
  private valueType(ctx: Ctx, type: TypeIR): Term {
    switch (type.kind) {
      case "int":
        return K.Int;
      case "union":
        return type.union!.sumType;
      case "generic":
        return this.resolvedTypeParam(ctx, type.typeParam!);
      case "vec":
        throw new ElaborateFailure("a loop cannot carry a vector: the extractor cannot name its length");
      case "boolean":
        throw new ElaborateFailure("`boolean` is only allowed as the type of a condition");
    }
  }

  /** The tuple type `A` itself: `Sigma (v0 : T0). Sigma (v1 : T1). … Unit`. */
  private tupleType(spec: TupleSpec, ctx: Ctx): Term {
    return this.tupleSuffix(spec, ctx, 0);
  }

  /**
   * `Sigma (v_i : T_i). … Unit`, written in the scope `[ctx, v_0 … v_{i-1}]` — the type of
   * the sub-tuple from component `i` on.
   */
  private tupleSuffix(spec: TupleSpec, ctx: Ctx, from: number): Term {
    let out: Term = K.Unit;
    for (let i = spec.components.length - 1; i >= from; i -= 1) {
      const component = spec.components[i]!;
      out = K.sigma(component.name, spec.typeAt(ctx, i, i), out);
    }
    return out;
  }

  /**
   * `⟨v0, ⟨v1, … ⟨vn-1, tt⟩⟩⟩ : A`, each pair annotated with the `Sigma` type of the suffix
   * it starts.  The annotation is the suffix *instantiated* with the preceding component
   * values — built as a beta-redex `(λ v_0 … v_{i-1}. Σ_i) v_0 … v_{i-1}` so that a dependent
   * component type (`InRange n`, `Vec T n_a`) is instantiated by the kernel itself.
   */
  private packTuple(spec: TupleSpec, ctx: Ctx, values: readonly Term[]): Term {
    if (values.length !== spec.components.length) {
      throw new ElaborateFailure("the state tuple and its component list disagree");
    }
    let out: Term = K.tt;
    for (let i = values.length - 1; i >= 0; i -= 1) {
      const binder = this.suffixLambda(spec, ctx, i);
      out = K.pair(K.appMany(binder, values.slice(0, i) as Term[]), values[i]!, out);
    }
    return out;
  }

  /** `λ v_0 … v_{i-1}. Σ_i`: the suffix type as a function of the components before it. */
  private suffixLambda(spec: TupleSpec, ctx: Ctx, from: number): Term {
    let out: Term = this.tupleSuffix(spec, ctx, from);
    for (let i = from - 1; i >= 0; i -= 1) {
      const component = spec.components[i]!;
      out = K.lam(component.name, spec.typeAt(ctx, i, i), out);
    }
    return out;
  }

  /** A `continue`: apply the loop's `ih` to the new state and the back-edge proofs. */
  private elabContinue(
    ctx: Ctx,
    hyps: readonly Hyp[],
    stmt: Extract<StmtIR, { kind: "continue" }>,
  ): Term {
    const frame = this.loopStack.find((entry) => entry.loop.id === stmt.loop.id);
    if (frame === undefined) throw new ElaborateFailure("a `continue` outside the loop it belongs to");
    const opts = this.optionsFor();
    this.withHyps(hyps, () => this.certifySites(ctx, hyps, stmt.sites, opts));
    const proofOf = (kind: ObligationKind): Term => {
      const site = stmt.sites.find((candidate) => candidate.kind === kind);
      if (site === undefined) throw new ElaborateFailure(`the back edge has no ${kind} obligation`);
      const proof = this.proofAt(site.id, ctx.binders.length);
      if (proof === undefined) throw new ElaborateFailure(`the ${kind} obligation of the back edge is missing`);
      return proof;
    };
    const values = stmt.values.map((entry) => exprTerm(ctx, entry.value, opts));
    const state = this.packTuple(frame.spec, ctx, values);
    return K.appMany(K.varTerm(deBruijnIndex(ctx, frame.ih)), [
      state,
      proofOf("measure-nonneg"),
      proofOf("measure-decrease"),
      proofOf("invariant-preserve"),
    ]);
  }

  // ---- recursive functions ------------------------------------------------

  /**
   * A recursive function as a `fixWf` over the *function's own parameters*:
   *
   * ```text
   * A     = Sigma (n : Int). Sigma (r_n : InRange n). Sigma (pre : …). … Unit
   * B     = fun (y : A) => pre_1(y) -> … -> Result(y)
   * m     = fun (x : A) => <@decreases>
   * step  = fun (x : A) (px : Le 0 (m x)) (ih : (y : A) -> Le 0 (m y) -> Lt (m y) (m x) -> B y)
   *             (pre_1 : …) => body
   * f     = fun (n : Int) (r_n : …) (pre : …) => fixWf A B m step x0 p0 pre
   * ```
   *
   * `B` absorbs the function's preconditions, so a recursive call is `ih x' p↧ p< pre'`: the
   * call site's `pre-call` obligation proves the preconditions of the *callee* at the
   * arguments, and the two measure sites prove the decrease.  The body is elaborated in a
   * context where every parameter (and every proof the signature introduced) stands for the
   * matching component of `x`, which is what makes `m x` and the call sites line up.
   */
  private elabRecursive(ctx: Ctx, hyps: readonly Hyp[]): Term {
    const opts = this.optionsFor();
    const measureExpr = this.fn.measure;
    if (measureExpr === undefined) {
      throw new ElaborateFailure("a recursive function needs a `@decreases` measure");
    }
    const binders = this.fn.signature.binders;
    const typeParams = binders.filter((binder) => binder.role === "type-param");
    const components = binders.filter((binder) => binder.role !== "type-param");
    if (binders.slice(0, typeParams.length).some((binder) => binder.role !== "type-param")) {
      throw new ElaborateFailure("the extractor emitted a type parameter after a value binder");
    }
    const typeParamCtx: Ctx = { ...ctx, binders: binders.slice(0, typeParams.length) };
    const spec = this.recursionSpec(ctx, binders, components);
    const tupleType = this.tupleType(spec, ctx);

    const tuple: Binder = { id: freshId(), name: "x", role: "local", type: tupleType };
    const xCtx = pushed(ctx, tuple);
    const restore = this.installProjections(tuple, components);
    try {
      // m x, and the measure-nonneg hypothesis the step receives.
      const measure = K.lam(
        "x",
        tupleType,
        this.withHyps(hypsAt(hyps, xCtx.binders.length), () => exprTerm(xCtx, measureExpr, opts)),
      );
      const pxType = K.Le(K.intLit(0n), K.app(shiftTerm(measure, 1), K.varTerm(0)));
      const px: Binder = { id: freshId(), name: "px", role: "loop-measure-nonneg", type: pxType };
      const measureCtx = pushed(xCtx, px);

      // B = fun (y : A) => pre_1(y) -> … -> Result(y).
      const y: Binder = { id: freshId(), name: "y", role: "local", type: tupleType };
      const yCtx = pushed(typeParamCtx, y);
      const restoreY = this.installProjections(y, components);
      let preTerms: Term[];
      let resultType: Term;
      try {
        preTerms = this.fn.signature.preconditions.map((fact) => exprTerm(yCtx, fact.prop, opts));
        resultType = this.resultTypeAt(yCtx);
      } finally {
        restoreY();
      }
      const predicate = K.lam("y", tupleType, arrowStack(preTerms, resultType));

      const ihType = K.pi(
        "y",
        shiftTerm(tupleType, 2),
        K.pi(
          "py",
          K.Le(K.intLit(0n), K.app(shiftTerm(measure, 3), K.varTerm(0))),
          K.pi(
            "pd",
            K.Lt(
              K.app(shiftTerm(measure, 4), K.varTerm(1)),
              K.app(shiftTerm(measure, 4), K.varTerm(3)),
            ),
            K.app(shiftTerm(predicate, 5), K.varTerm(2)),
          ),
        ),
      );
      const ih: Binder = { id: freshId(), name: "ih", role: "local", type: ihType };
      let bodyCtx = pushed(measureCtx, ih);
      const bodyDepth = bodyCtx.binders.length;

      // The preconditions are the arguments of `B x`, so the body is under their binders.
      const preLambdas: { name: string; type: Term }[] = [];
      const preHyps: Hyp[] = [];
      this.fn.signature.preconditions.forEach((fact, index) => {
        const type = this.withHyps(hypsAt(hyps, bodyCtx.binders.length), () =>
          exprTerm(bodyCtx, fact.prop, opts),
        );
        const binder: Binder = {
          id: freshId(),
          name: fact.binder?.name ?? `pre${index}`,
          role: "hypothesis",
          type,
        };
        preLambdas.push({ name: binder.name, type });
        bodyCtx = pushed(bodyCtx, binder);
        preHyps.push({
          term: shiftTerm(type, 1),
          proof: K.varTerm(0),
          depth: bodyCtx.binders.length,
          origin: "pre",
        });
      });

      const frame: RecursionContext = { tuple, ih, measure, binders: components, spec };
      this.recursion = frame;
      let body: Term;
      try {
        body = this.elabStmts(
          bodyCtx,
          dedupeHyps([...this.recursionHyps(bodyCtx, components, spec), ...preHyps]),
          this.fn.body,
        );
      } finally {
        this.recursion = null;
      }
      let step = body;
      // Inside-out, so the first precondition is the outermost binder — the order `B`'s
      // arrow stack and the application below expect.
      for (let i = preLambdas.length - 1; i >= 0; i -= 1) {
        const lambda = preLambdas[i]!;
        step = K.lam(lambda.name, lambda.type, step);
      }
      step = K.lam("ih", ihType, step);
      step = K.lam("px", pxType, step);
      step = K.lam("x", tupleType, step);

      // The entry: the parameters themselves are the argument tuple.
      const start = this.packTuple(
        spec,
        ctx,
        components.map((binder) => K.varTerm(deBruijnIndex(ctx, binder))),
      );
      const p0 =
        this.proveAux(
          ctx,
          hyps,
          K.Le(K.intLit(0n), K.app(measure, start)),
          "measure-nonneg",
          this.fn.nameSpan,
          `the entry measure of \`${this.fn.name}\``,
        ) ?? K.tt;
      const preProofs = this.fn.signature.preconditions.map((fact) =>
        fact.binder === undefined ? K.tt : K.varTerm(deBruijnIndex(ctx, fact.binder)),
      );
      void bodyDepth;
      return K.appMany(K.FixWf(0, tupleType, predicate, measure, step, start, p0), preProofs);
    } finally {
      restore();
    }
  }

  /** The tuple telescope of a recursive function: its signature binders, in order. */
  private recursionSpec(ctx: Ctx, binders: readonly Binder[], components: readonly Binder[]): TupleSpec {
    void ctx;
    const componentAt = new Map<number, number>();
    const positionOf = new Map<number, number>();
    binders.forEach((binder, position) => {
      positionOf.set(binder.id, position);
      const index = components.findIndex((candidate) => candidate.id === binder.id);
      if (index >= 0) componentAt.set(position, index);
    });
    const list: Component[] = components.map((binder) => ({
      name: binder.name,
      type: binder.type,
      path: componentPath(componentAt.get(positionOf.get(binder.id)!)!),
    }));
    return {
      components: list,
      typeAt: (at, bound, index) => {
        // `binder.type` is written in the context of the *preceding* signature binders, so
        // the free index of binder `position` is `index - 1 - position`.
        const source = components[index]!;
        const own = positionOf.get(source.id)!;
        const args = new Map<number, Term>();
        binders.forEach((binder, position) => {
          if (position >= own) return;
          const component = componentAt.get(position);
          if (component === undefined) {
            // A type parameter: it stays an ambient binder, lifted past the telescope's own.
            args.set(own - 1 - position, K.varTerm(deBruijnIndex(at, binder) + bound));
          } else if (component < bound) {
            args.set(own - 1 - position, K.varTerm(bound - 1 - component));
          }
        });
        return substituteFree(source.type, args);
      },
    };
  }

  /**
   * Register the signature binders as the components of `tuple`, for the duration of a walk:
   * every slot that mentions one resolves to the projection of the tuple, and every *term*
   * the extractor stored that mentions one (a binder type, the result type) is rewritten the
   * same way by `fromExtractor`.  Returns the undo.
   */
  private installProjections(tuple: Binder, binders: readonly Binder[]): () => void {
    const savedSlots: [number, ((at: Ctx) => Term | undefined) | undefined][] = [];
    const savedExt: [number, ((at: Ctx) => Term | undefined) | undefined][] = [];
    const restore = (): void => {
      for (const [id, entry] of savedSlots) {
        if (entry === undefined) this.inlineSlots.delete(id);
        else this.inlineSlots.set(id, entry);
      }
      for (const [position, entry] of savedExt) {
        if (entry === undefined) this.inlineExt.delete(position);
        else this.inlineExt.set(position, entry);
      }
    };
    binders.forEach((binder, index) => {
      const path = componentPath(index);
      const termOf = (at: Ctx): Term | undefined =>
        at.binders.some((candidate) => candidate.id === tuple.id)
          ? project(K.varTerm(deBruijnIndex(at, tuple)), path)
          : undefined;
      savedSlots.push([binder.id, this.inlineSlots.get(binder.id)]);
      this.inlineSlots.set(binder.id, termOf);
      const position = this.extOf.get(binder.id);
      if (position !== undefined) {
        savedExt.push([position, this.inlineExt.get(position)]);
        this.inlineExt.set(position, termOf);
      }
    });
    return restore;
  }

  /** The signature's own facts, restated about the argument tuple's components. */
  private recursionHyps(ctx: Ctx, binders: readonly Binder[], spec: TupleSpec): Hyp[] {
    const depth = ctx.binders.length;
    const opts = this.optionsFor();
    const out: Hyp[] = [];
    const projection = (binder: Binder): Term | undefined => this.inlineSlots.get(binder.id)?.(ctx);
    for (const fact of this.fn.signature.preconditions) {
      const proof = fact.binder === undefined ? undefined : projection(fact.binder);
      if (proof === undefined) continue;
      try {
        out.push({ term: exprTerm(ctx, fact.prop, opts), proof, depth, origin: "pre" });
      } catch {
        // The proposition cannot be built; the site that needs it reports its own failure.
      }
    }
    binders.forEach((binder, index) => {
      const value = projection(binder);
      if (value === undefined) return;
      if (binder.role === "in-range") {
        const param = binders[index - 1];
        const target = param === undefined ? undefined : projection(param);
        if (target === undefined) return;
        out.push({ term: K.InRange(target), proof: value, depth, origin: "param-in-range" });
        return;
      }
      if (binder.role === "vec-len") {
        const vec = binders[index + 1];
        const vector = vec === undefined ? undefined : projection(vec);
        if (vector === undefined || vec === undefined) return;
        const vecType = this.fromExtractor(ctx, spec.components[index]!.type, this.fn.signature.binders.length);
        const elem = vecType.tag === "Prim" ? vecType.args[0] : undefined;
        if (elem === undefined) return;
        out.push({
          term: K.And(K.Le(K.intLit(0n), value), K.Le(value, K.intLit(K.MAX_VEC_LEN))),
          proof: K.VecBounds(elem, value, vector),
          depth,
          origin: "vec-bounds",
        });
      }
    });
    return out;
  }

  // ---- statements ---------------------------------------------------------

  private elabStmts(ctx: Ctx, hyps: readonly Hyp[], stmts: readonly StmtIR[]): Term {
    for (let i = 0; i < stmts.length; i += 1) {
      const stmt = stmts[i]!;
      switch (stmt.kind) {
        case "nop":
          continue;
        case "expr": {
          this.withHyps(hyps, () => this.prepare(ctx, hyps, stmt.expr, this.optionsFor()));
          continue;
        }
        case "local": {
          const depth = ctx.binders.length;
          const value = this.elabExpr(ctx, hyps, stmt.value);
          const inner = this.pushExt(value.ctx, stmt.binder);
          // A local whose value carries no proof argument is substituted at every use: it is
          // still bound with a `let` (so the kernel term is unchanged, up to zeta), but a
          // goal that mentions it by name mentions its value instead, which is what lets a
          // `divFloorSpec` fact about `(lo + hi) / 2` line up with `let mid = …`.
          const inlinable = !containsProofCarrier(stmt.value);
          const binder = stmt.binder;
          const term = value.term;
          if (inlinable) {
            this.inlineSlots.set(binder.id, (at) =>
              at.binders.some((candidate) => candidate.id === binder.id)
                ? shiftTerm(term, at.binders.length - depth)
                : undefined,
            );
          }
          let rest: Term;
          try {
            rest = this.elabStmts(
              inner,
              hypsAt([...hyps, ...value.facts], inner.binders.length),
              stmts.slice(i + 1),
            );
          } finally {
            if (inlinable) this.inlineSlots.delete(binder.id);
            value.undo();
          }
          return value.wrap(
            K.letTerm(stmt.binder.name, this.binderTypeAt(value.ctx, stmt.binder), value.term, rest),
          );
        }
        case "return":
          return this.elabReturn(ctx, hyps, stmt);
        case "if":
          return this.elabIf(ctx, hyps, stmt);
        case "switch":
          return this.elabSwitch(ctx, hyps, stmt);
        case "loop":
          return this.elabLoop(ctx, hyps, stmt.loop);
        case "continue":
          return this.elabContinue(ctx, hyps, stmt);
        case "assign":
          this.internal(
            stmt.span,
            `\`${this.fn.name}\` assigns to a variable that is neither a loop-carried variable nor a ` +
              `fresh local; this is a gap in the extraction`,
          );
          return K.tt;
      }
    }
    this.internal(this.fn.span, `not every path through \`${this.fn.name}\` ends in a \`return\``);
    return K.tt;
  }

  /**
   * Certify everything the expression needs, then build its term and collect its facts.
   *
   * A proof-carrying call is bound with a `let` first (innermost call first), and the
   * extended context is what the goals are built in: this is what keeps a `@post` or a
   * `range` goal about a recursive call a *variable* instead of a term with certificates in
   * it.  `wrap` emits the `let`s around the statement the value belongs to.
   */
  private elabExpr(
    ctx: Ctx,
    hyps: readonly Hyp[],
    e: ExprIR,
  ): { term: Term; facts: Hyp[]; ctx: Ctx; wrap: (body: Term) => Term; undo: () => void } {
    const opts = this.optionsFor();
    const binds: { binder: Binder; value: Term }[] = [];
    const bound: ExprIR[] = [];
    let work = ctx;
    let callHyps = hypsAt(hyps, ctx.binders.length);
    for (const node of callNodesIn(e)) {
      // The call's own obligations (`pre-call`, the two measure sites) and its arguments'
      // must be certified before its term can be built; the facts that walk derives are
      // discarded here, because they would be stated about the *unbound* call.
      this.withHyps(callHyps, () => this.prepare(work, callHyps, node, opts));
      const info = this.callInfo(work, node, opts);
      const type = info.packedType ?? this.valueTypeOf(work, node, info.packed);
      const binder: Binder = { id: freshId(), name: "call", role: "local", type };
      this.boundCalls.set(callSiteKey(node), { binder, depth: work.binders.length, applied: info.applied });
      bound.push(node);
      binds.push({ binder, value: info.packed });
      work = pushed(work, binder);
      // Now that the call is a variable, its facts (its result is `InRange`, the callee's
      // postconditions) are worth keeping for the *next* call's obligations.
      const atBound = hypsAt(callHyps, work.binders.length);
      callHyps = [
        ...atBound,
        ...this.withHyps(atBound, () => this.derivedFacts(work, node, atBound, opts)),
      ];
    }
    const shifted = hypsAt(hyps, work.binders.length);
    const facts = this.withHyps(shifted, () => this.prepare(work, shifted, e, opts));
    const term = this.withHyps([...shifted, ...facts], () => exprTerm(work, e, opts));
    const wrap = (body: Term): Term => {
      let out = body;
      for (let i = binds.length - 1; i >= 0; i -= 1) {
        const bind = binds[i]!;
        out = K.letTerm(bind.binder.name, bind.binder.type, bind.value, out);
      }
      return out;
    };
    // The caller keeps the bindings alive for the whole statement (`@post` is certified
    // after the value was bound) and undoes them when it is done.
    const undo = (): void => {
      for (const node of bound) this.boundCalls.delete(callSiteKey(node));
    };
    return { term, facts, ctx: work, wrap, undo };
  }

  private elabReturn(ctx: Ctx, hyps: readonly Hyp[], stmt: Extract<StmtIR, { kind: "return" }>): Term {
    return this.elabReturnValue(ctx, hyps, stmt.value, stmt.site);
  }

  /**
   * Elaborate a `return`.  When the returned expression is itself a conditional, the packing
   * (and with it the `@post` obligation) is pushed into the branches: `return c ? a : b`
   * becomes `ifLe … (h => ⟨a, post-a⟩) (h' => ⟨b, post-b⟩)`, so each postcondition is
   * certified under its own branch hypothesis.  A conditional *nested* inside the returned
   * expression is not split (and the postcondition then has no certificate).
   */
  private elabReturnValue(ctx: Ctx, hyps: readonly Hyp[], valueExpr: ExprIR, site: ObligationSite): Term {
    if (valueExpr.kind === "cond" && valueExpr.cond !== undefined) {
      const cond = valueExpr.cond;
      const depth = ctx.binders.length;
      const conditionFacts = this.withHyps(hyps, () => this.prepare(ctx, hyps, cond.expr, this.optionsFor()));
      const base = [...hyps, ...conditionFacts];
      const opts = this.optionsFor();
      const motive = this.resultTypeAt(ctx);
      if (cond.thenExpr === undefined || cond.elseExpr === undefined) {
        throw new ElaborateFailure("a returned conditional has no branches");
      }
      if (cond.tagTest !== undefined) {
        const union = cond.tagTest.union;
        const thenVariant = cond.thenNarrowings[0]?.variant ?? cond.tagTest.variant;
        const elseVariant = cond.elseNarrowings[0]?.variant ?? otherVariant(union, cond.tagTest.variant);
        const thenExpr = cond.thenExpr;
        const elseExpr = cond.elseExpr;
        return this.caseSplit(ctx, base, cond.tagTest.subject, union, [
          {
            variant: thenVariant,
            binder: cond.thenBinder,
            build: (bctx, bhyps) => this.elabReturnValue(bctx, bhyps, thenExpr, site),
          },
          {
            variant: elseVariant,
            binder: cond.elseBinder,
            build: (bctx, bhyps) => this.elabReturnValue(bctx, bhyps, elseExpr, site),
          },
        ]);
      }
      const [a, b] = this.ifLeOperands(ctx, cond.expr, opts);
      const thenBinder = this.branchBinder(cond.thenBinder, K.Le(a, b));
      const elseBinder = this.branchBinder(cond.elseBinder, K.Lt(b, a));
      const thenTerm = this.elabReturnValue(
        this.pushExt(ctx, thenBinder),
        [
          ...hypsAt(base, depth + 1),
          { term: shiftTerm(K.Le(a, b), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
        ],
        cond.thenExpr,
        site,
      );
      const elseTerm = this.elabReturnValue(
        this.pushExt(ctx, elseBinder),
        [
          ...hypsAt(base, depth + 1),
          { term: shiftTerm(K.Lt(b, a), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
        ],
        cond.elseExpr,
        site,
      );
      return K.IfLe(
        0,
        motive,
        a,
        b,
        K.lam(cond.thenBinder.name, K.Le(a, b), thenTerm),
        K.lam(cond.elseBinder.name, K.Lt(b, a), elseTerm),
      );
    }

    const value = this.elabExpr(ctx, hyps, valueExpr);
    try {
      const atValue = hypsAt([...hyps, ...value.facts], value.ctx.binders.length);
      const bound = this.bindReturnValue(value.ctx, atValue, valueExpr, value.term, value.facts);
      const proof = this.withHyps(bound.hyps, () =>
        this.certifyPost(bound.ctx, bound.hyps, site, bound.surface),
      );
      return value.wrap(bound.wrap(this.packResult(bound.ctx, bound.surface, proof, valueExpr)));
    } finally {
      value.undo();
    }
  }

  /**
   * Bind the returned value (and the facts derived about it) in `let`s, so that the
   * postcondition is stated over a *variable* rather than over a term that carries proof
   * arguments.  `certify` decomposes a goal by quoting it; a certificate term stored inside
   * such a term is quoted at the wrong depth and the obligation then looks like a dependent
   * `Sigma`, with no proof to be found.  Binding the value also gives each derived fact a
   * variable to be named by, which is what the hypotheses of the `@post` obligation need.
   */
  private bindReturnValue(
    ctx: Ctx,
    hyps: readonly Hyp[],
    valueExpr: ExprIR,
    valueTerm: Term,
    facts: readonly Hyp[],
  ): { ctx: Ctx; hyps: Hyp[]; surface: Term; wrap: (body: Term) => Term } {
    const isCall = valueExpr.kind === "call" && valueExpr.callee !== undefined && valueExpr.callee.kind !== "prelude";
    const root = isCall ? this.callTerm(ctx, valueExpr, this.optionsFor()) : valueTerm;
    const surfaceOf = (term: Term): Term => (isCall ? project(term, valueExpr.layout?.valuePath ?? []) : term);
    // Binding is only needed when the value's own term carries proof arguments; a plain
    // `-x` or `a.side` stays inline so that the linear reasoning over the original
    // parameters still applies to the postcondition.
    if (!containsProofCarrier(valueExpr)) {
      return { ctx, hyps: hypsAt(hyps, ctx.binders.length), surface: surfaceOf(root), wrap: (body) => body };
    }

    const depth = ctx.binders.length;
    const valueType = this.valueTypeOf(ctx, valueExpr, root);
    const binder: Binder = { id: freshId(), name: "result", role: "local", type: valueType };
    let current = pushed(ctx, binder);
    const pattern = shiftTerm(root, 1);

    const bindings: { binder: Binder; type: Term; value: Term }[] = [];
    let currentHyps: Hyp[] = [...hypsAt(hyps, depth + 1), ...hypsAt(facts, depth + 1)];
    facts.forEach((fact, index) => {
      const shift = current.binders.length - depth - 1;
      // The fact lives at the ambient depth; under the value binder the term it is about is
      // the bound variable, so rewrite it there and only then move it past the earlier fact
      // binders.
      const prop = shiftTerm(replaceSubterm(shiftTerm(fact.term, 1), pattern, K.varTerm(0)), shift);
      const proof = shiftTerm(replaceSubterm(shiftTerm(fact.proof, 1), pattern, K.varTerm(0)), shift);
      const proofBinder: Binder = { id: freshId(), name: `f${index}`, role: "hypothesis", type: prop };
      bindings.push({ binder: proofBinder, type: prop, value: proof });
      current = pushed(current, proofBinder);
      currentHyps = [
        ...currentHyps,
        { term: shiftTerm(prop, 1), proof: K.varTerm(0), depth: current.binders.length, origin: fact.origin },
      ];
    });

    const surface = surfaceOf(K.varTerm(deBruijnIndex(current, binder)));
    return {
      ctx: current,
      hyps: currentHyps,
      surface,
      wrap: (body: Term): Term => {
        let plan = body;
        for (let i = bindings.length - 1; i >= 0; i -= 1) {
          const binding = bindings[i]!;
          plan = K.letTerm(binding.binder.name, binding.type, binding.value, plan);
        }
        return K.letTerm(binder.name, valueType, root, plan);
      },
    };
  }

  /** The kernel type of a returned value, for the `let` that binds it. */
  private valueTypeOf(ctx: Ctx, valueExpr: ExprIR, root: Term): Term {
    if (valueExpr.kind === "call" && valueExpr.callee?.kind === "prelude") {
      return K.Int;
    }
    if (valueExpr.kind === "call" && valueExpr.callee !== undefined) {
      const info = this.callInfo(ctx, valueExpr, this.optionsFor());
      if (info.packedType !== undefined) return info.packedType;
    }
    switch (valueExpr.type.kind) {
      case "int":
        return K.Int;
      case "union":
        return valueExpr.type.union!.sumType;
      case "generic":
        return this.resolvedTypeParam(ctx, valueExpr.type.typeParam!);
      case "vec": {
        if (valueExpr.vecLength === undefined) throw new ElaborateFailure("a returned vector has no length");
        return K.Vec(this.elemType(ctx, valueExpr.type.elem!), exprTerm(ctx, valueExpr.vecLength, this.optionsFor()));
      }
      case "boolean":
        throw new ElaborateFailure("`boolean` is only allowed as the type of a condition");
    }
    void root;
  }

  /** The packed `Sigma` result of `ResultLayout`. */
  private packResult(ctx: Ctx, value: Term, postProof: Term, valueExpr: ExprIR): Term {
    const layout = this.fn.signature.result.layout;
    const sigmaType = this.resultTypeAt(ctx);
    switch (layout.shape) {
      case "int":
        return K.pair(sigmaType, value, postProof);
      case "vec": {
        if (valueExpr.vecLength === undefined) throw new ElaborateFailure("a returned vector has no length");
        const length = exprTerm(ctx, valueExpr.vecLength, this.optionsFor());
        if (sigmaType.tag !== "Sigma") throw new ElaborateFailure("the result type is not a Sigma");
        if (this.fn.signature.result.posts.length === 0) return K.pair(sigmaType, length, value);
        return K.pair(sigmaType, length, K.pair(instantiateTop(sigmaType.second, length), value, postProof));
      }
      case "generic":
      case "union":
        return value;
    }
  }

  private elabIf(ctx: Ctx, hyps: readonly Hyp[], stmt: Extract<StmtIR, { kind: "if" }>): Term {
    const cond = stmt.cond;
    const depth = ctx.binders.length;
    const conditionFacts = this.withHyps(hyps, () => this.prepare(ctx, hyps, cond.expr, this.optionsFor()));
    const base = [...hyps, ...conditionFacts];

    if (cond.tagTest !== undefined) {
      const union = cond.tagTest.union;
      const thenVariant = cond.thenNarrowings[0]?.variant ?? cond.tagTest.variant;
      const elseVariant = cond.elseNarrowings[0]?.variant ?? otherVariant(union, cond.tagTest.variant);
      const thenBody = stmt.then;
      const elseBody = stmt.otherwise;
      return this.caseSplit(ctx, base, cond.tagTest.subject, union, [
        {
          variant: thenVariant,
          binder: cond.thenBinder,
          build: (bctx, bhyps) => this.elabStmts(bctx, bhyps, thenBody),
        },
        {
          variant: elseVariant,
          binder: cond.elseBinder,
          build: (bctx, bhyps) => this.elabStmts(bctx, bhyps, elseBody),
        },
      ]);
    }

    const [a, b] = this.ifLeOperands(ctx, cond.expr, this.optionsFor());
    const thenBinder = this.branchBinder(cond.thenBinder, K.Le(a, b));
    const elseBinder = this.branchBinder(cond.elseBinder, K.Lt(b, a));
    const thenCtx = this.pushExt(ctx, thenBinder);
    const elseCtx = this.pushExt(ctx, elseBinder);
    const thenTerm = this.elabStmts(
      thenCtx,
      [
        ...hypsAt(base, depth + 1),
        { term: shiftTerm(K.Le(a, b), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
      ],
      stmt.then,
    );
    const elseTerm = this.elabStmts(
      elseCtx,
      [
        ...hypsAt(base, depth + 1),
        { term: shiftTerm(K.Lt(b, a), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
      ],
      stmt.otherwise,
    );
    return K.IfLe(
      0,
      this.resultTypeAt(ctx),
      a,
      b,
      K.lam(cond.thenBinder.name, K.Le(a, b), thenTerm),
      K.lam(cond.elseBinder.name, K.Lt(b, a), elseTerm),
    );
  }

  private elabSwitch(ctx: Ctx, hyps: readonly Hyp[], stmt: Extract<StmtIR, { kind: "switch" }>): Term {
    const union = stmt.union;
    const branches: CaseBranch[] = [];
    for (const variant of union.variants) {
      const matched = stmt.cases.find((c) => c.variant?.index === variant.index);
      if (matched === undefined || matched.payload === null) {
        this.internal(stmt.span, `the case \`${variant.tag}\` of this switch is missing`);
        return K.tt;
      }
      const body = matched.body;
      branches.push({
        variant,
        binder: matched.payload,
        build: (bctx, bhyps) => this.elabStmts(bctx, bhyps, body),
      });
    }
    return this.caseSplit(ctx, hyps, stmt.subject, union, branches);
  }

  // ---- case splits --------------------------------------------------------

  private resultTypeAt(ctx: Ctx): Term {
    return this.fromExtractor(ctx, this.fn.signature.result.term, this.fn.signature.binders.length);
  }

  /**
   * A case split on a union discriminant.  Conditional *preconditions* testing the same
   * subject are eliminated with it: the split's motive is `preAt(s') -> … -> Result`, so
   * each branch gets the branch-specific precondition as a hypothesis and the split is
   * applied to the precondition's proof.
   */
  private caseSplit(
    ctx: Ctx,
    hyps: readonly Hyp[],
    subject: Slot,
    union: UnionIR,
    branches: readonly CaseBranch[],
  ): Term {
    const depth = ctx.binders.length;
    const opts = this.optionsFor();
    const conditional = hyps.filter(
      (hyp) =>
        hyp.prop !== undefined &&
        hyp.prop.kind === "cond" &&
        hyp.prop.cond?.tagTest !== undefined &&
        sameSlot(hyp.prop.cond.tagTest.subject, subject),
    );

    const preTerms: Term[] = [];
    if (conditional.length > 0) {
      const prime: Binder = { id: freshId(), name: "s'", role: "local", type: union.sumType };
      const primeCtx = pushed(ctx, prime);
      for (const hyp of conditional) {
        const replaced = mapSlots(hyp.prop!, (slot) =>
          sameSlot(slot, subject) ? { kind: "binder", binder: prime } : slot,
        );
        preTerms.push(this.withHyps(hypsAt(hyps, depth + 1), () => exprTerm(primeCtx, replaced, opts)));
      }
    }

    const build = (branch: CaseBranch): Term => {
      let inner = this.pushExt(ctx, branch.binder);
      let branchHyps: Hyp[] = [...hypsAt(hyps, depth + 1)];
      const lambdas: { name: string; domain: Term }[] = [];
      for (let k = 0; k < conditional.length; k += 1) {
        const hyp = conditional[k]!;
        const test = hyp.prop!.cond!.tagTest!;
        const positive = (branch.variant.index === test.variant.index) === test.positive;
        const source = positive ? hyp.prop!.cond!.thenExpr : hyp.prop!.cond!.elseExpr;
        if (source === undefined) throw new ElaborateFailure("a conditional precondition has no branch expression");
        const replaced = mapSlots(source, (slot) =>
          slot.kind === "payload"
            ? { kind: "payload", union, variant: branch.variant, payload: branch.binder }
            : slot,
        );
        const domain = this.withHyps(branchHyps, () => exprTerm(inner, replaced, opts));
        const binder: Binder = {
          id: freshId(),
          name: `hpre${k}`,
          role: "hypothesis",
          type: domain,
        };
        lambdas.push({ name: binder.name, domain });
        // The hypothesis is the new variable; both terms move to the context that binds it.
        branchHyps = [
          ...branchHyps,
          { term: shiftTerm(domain, 1), proof: K.varTerm(0), depth: inner.binders.length + 1, origin: "pre" },
        ];
        inner = pushed(inner, binder);
      }
      const result = branch.build(inner, branchHyps);
      let out = result;
      for (let k = lambdas.length - 1; k >= 0; k -= 1) {
        out = K.lam(lambdas[k]!.name, lambdas[k]!.domain, out);
      }
      return K.lam(branch.binder.name, branch.variant.recordType, out);
    };

    const ordered = [...branches].sort((a, b) => a.variant.index - b.variant.index);
    const left = ordered[0]!;
    const right = ordered[1];
    if (right === undefined) throw new ElaborateFailure("a case split needs two branches");
    const motive =
      conditional.length === 0
        ? K.lam("_", union.sumType, shiftTerm(this.resultTypeAt(ctx), 1))
        : K.lam("s'", union.sumType, arrowsTo(preTerms, shiftTerm(this.resultTypeAt(ctx), 1)));
    const caseTerm = K.SumCase(
      0,
      left.variant.recordType,
      right.variant.recordType,
      motive,
      build(left),
      build(right),
      slotTerm(ctx, subject, opts),
    );
    if (conditional.length === 0) return caseTerm;
    return K.appMany(caseTerm, conditional.map((hyp) => hypAt(hyp, depth).proof));
  }

  // ---- helpers ------------------------------------------------------------

  /** `[a, b]` for `ifLe`, mirroring `fragment.ts`'s private `ifLeOperands`. */
  private ifLeOperands(ctx: Ctx, cond: ExprIR, opts: TermOptions): [Term, Term] {
    const lhs = exprTerm(ctx, cond.args[0]!, opts);
    const rhs = exprTerm(ctx, cond.args[1]!, opts);
    switch (cond.kind) {
      case "lt":
        return [K.Add(lhs, K.intLit(1n)), rhs];
      case "gt":
        return [K.Add(rhs, K.intLit(1n)), lhs];
      case "ge":
        return [rhs, lhs];
      case "neq":
        return [K.Add(lhs, K.intLit(1n)), rhs];
      default:
        return [lhs, rhs];
    }
  }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function otherVariant(union: UnionIR, variant: VariantIR): VariantIR {
  return union.variants.find((v) => v.index !== variant.index) ?? variant;
}

function obligationMessage(kind: ObligationKind, text: string): string {
  switch (kind) {
    case "post":
      return `postcondition \`${text}\` may not hold`;
    case "pre-call":
      return `a precondition of the call may not hold: \`${text}\``;
    case "index":
      return `the index may be out of bounds: \`${text}\` may not hold`;
    case "slice":
      return `the slice bounds \`${text}\` may not hold`;
    case "append-length":
      return `the concatenated array length may exceed 4294967295: \`${text}\` may not hold`;
    case "range":
      return `the value may leave the safe integer range: \`${text}\` may not hold`;
    case "measure-nonneg":
      return `the termination measure may be negative: \`${text}\` may not hold`;
    case "measure-decrease":
      return `the termination measure may not decrease: \`${text}\` may not hold`;
    case "invariant-init":
      return `the loop invariant may not hold on entry: \`${text}\` may not hold`;
    case "invariant-preserve":
      return `the loop invariant may not be preserved: \`${text}\` may not hold`;
  }
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/**
 * Elaborate one function and, when the kernel accepts it, add it to the environment as a
 * `def` (so same-file calls resolve and `axiomsUsed` stays `[]`).  A function that is not
 * certified is admitted as an `external` declaration instead (when the source hash is
 * known), so its callers can still be elaborated — they are marked as depending on an
 * uncertified function.
 */
export function elaborateFunction(
  env: K.Env,
  fn: FunctionIR,
  options: ElaborateOptions = {},
): ElaborationOutcome {
  try {
    return new Elaborator(env, fn, options).run();
  } catch (error) {
    const detail = error instanceof Error ? error.message : String(error);
    const diagnostic: Diagnostic = {
      kind: "internal",
      severity: "error",
      span: fn.nameSpan,
      message: `could not elaborate \`${fn.name}\`: ${detail}`,
    };
    return {
      result: {
        name: fn.name,
        status: "failed",
        certified: false,
        type: fn.signature.type,
        obligations: [],
        diagnostics: [diagnostic],
        imports: fn.imports,
        dependsOnUncertified: [],
      },
      env,
      declarationError: diagnostic,
    };
  }
}
