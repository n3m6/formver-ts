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
}

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
}

// ---------------------------------------------------------------------------
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
  if (e.kind === "call" || e.kind === "index" || e.kind === "slice" || e.kind === "append") return true;
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

function dedupeHyps(hyps: readonly Hyp[]): Hyp[] {
  const seen = new Set<string>();
  const out: Hyp[] = [];
  for (const hyp of hyps) {
    const key = `${hyp.depth}|${K.formatTerm(hyp.term)}|${K.formatTerm(hyp.proof)}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(hyp);
  }
  return out;
}

function conjunctionProjection(index: number): number[] {
  const path: number[] = [];
  for (let i = 0; i < index; i += 1) path.push(1, 0);
  return path;
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

class Elaborator {
  private readonly env: K.Env;
  private readonly fn: FunctionIR;
  private readonly options: ElaborateOptions;
  private readonly diagnostics: Diagnostic[] = [];
  /** Proof per site id; a placeholder sits here for a site that is not certified. */
  private readonly proofs = new Map<number, Term>();
  private readonly outcomes = new Map<number, ObligationOutcome>();
  private readonly visited = new Set<number>();
  /** Hypotheses of the expression currently being built (the `override` hook reads this). */
  private activeHyps: readonly Hyp[] = [];
  /** Built call applications, keyed by the call node (see `callInfo`). */
  private readonly callCache = new Map<
    ExprIR,
    { packed: Term; packedType?: Term; applied: Map<number, Term> }
  >();
  private auxCount = 0;
  private readonly dependsOnUncertified = new Set<string>();

  constructor(env: K.Env, fn: FunctionIR, options: ElaborateOptions) {
    this.env = env;
    this.fn = fn;
    this.options = options;
  }

  // ---- entry point --------------------------------------------------------

  run(): ElaborationOutcome {
    if (this.fn.recursive || this.fn.loops.length > 0) {
      this.internal(
        this.fn.nameSpan,
        `\`${this.fn.name}\` uses ${this.fn.recursive ? "recursion" : "a loop"}, and loop and ` +
          `recursive-function elaboration is not implemented yet (milestone 7 part B); only ` +
          `the straight-line fragment is elaborated`,
      );
      return this.finish("failed");
    }

    const ctx: Ctx = { binders: this.fn.signature.binders, facts: [], narrowings: [], ids: new Ids() };
    const hyps = this.signatureHyps(ctx);

    let body: Term;
    try {
      body = this.elabStmts(ctx, hyps, this.fn.body);
      this.sweep(ctx, hyps);
    } catch (error) {
      this.internal(
        this.fn.nameSpan,
        `could not elaborate \`${this.fn.name}\`: ${error instanceof Error ? error.message : String(error)}`,
      );
      return this.finish("failed");
    }

    let term = body;
    for (let i = this.fn.signature.binders.length - 1; i >= 0; i -= 1) {
      const binder = this.fn.signature.binders[i]!;
      term = K.lam(binder.name, binder.type, term);
    }

    const failed = [...this.outcomes.values()].some((o) => o.status === "failed");
    if (failed) return this.finish("failed", term);

    const smtOnly = [...this.outcomes.values()].some((o) => o.status === "smt-only");
    const checked = K.checkType(this.env, term, this.fn.signature.type);
    if (!checked.ok) {
      if (smtOnly) return this.finish("smt-only", term);
      this.internal(
        this.fn.nameSpan,
        `the kernel rejected the elaborated term of \`${this.fn.name}\`: ${K.formatKernelError(checked.error)}`,
      );
      return this.finish("failed", term);
    }
    return this.finish(smtOnly ? "smt-only" : "certified", term);
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
      const elem = shiftTerm(vec.type.args[0]!, depth - (i + 1));
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
      // The binder's own type *is* the proposition its variable proves; using it (shifted
      // to this context) keeps the hypothesis and the proof in step even where the
      // extractor's rendering differs (an `if (a === b)` branch, for example, binds
      // `Le a b`, not `Eq Int a b`).
      const position = ctx.binders.findIndex((binder) => binder.id === fact.binder!.id);
      if (position < 0) return null;
      return {
        term: shiftTerm(fact.binder.type, depth - position),
        proof: K.varTerm(deBruijnIndex(ctx, fact.binder)),
        depth,
        prop: fact.prop,
        origin: fact.origin,
      };
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
    for (let i = 0; i < ctx.binders.length; i += 1) {
      const vec = ctx.binders[i]!;
      if (vec.role !== "param" || vec.type.tag !== "Prim" || vec.type.op !== K.OP_VEC) continue;
      const second = vec.type.args[1];
      if (second === undefined || second.tag !== "Var") continue;
      if (second.index + (depth - (i + 1)) !== lenIndex) continue;
      const n = K.varTerm(lenIndex);
      return {
        term: K.And(K.Le(K.intLit(0n), n), K.Le(n, K.intLit(K.MAX_VEC_LEN))),
        proof: K.VecBounds(shiftTerm(vec.type.args[0]!, depth - (i + 1)), n, K.varTerm(deBruijnIndex(ctx, vec))),
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
    const proof = this.proofs.get(node.siteId);
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
      proofs: this.proofs,
      override: (ctx, e, opts) => this.overrideTerm(ctx, e, opts),
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
  ): { packed: Term; packedType?: Term; applied: Map<number, Term> } {
    const cached = this.callCache.get(e);
    if (cached !== undefined) return cached;
    const callee = e.callee;
    if (callee === undefined) throw new ElaborateFailure("a call expression without a callee");
    if (callee.kind === "prelude") {
      const built = callee.builtin!.build(e.args.map((arg) => exprTerm(ctx, arg, opts)));
      const info: { packed: Term; packedType?: Term; applied: Map<number, Term> } = {
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

    const preProofs = this.preCallProofs(e);
    const typeArgs = this.typeArguments(ctx, signature, e.args);
    const applied = new Map<number, Term>();
    const ordered: Term[] = [];
    let preIndex = 0;
    let previousParam: Binder | undefined;
    for (let i = 0; i < signature.binders.length; i += 1) {
      const binder = signature.binders[i]!;
      const push = (term: Term): void => {
        applied.set(binder.id, term);
        ordered.push(term);
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
    const info: { packed: Term; packedType?: Term; applied: Map<number, Term> } = {
      packed: K.appMany(K.constTerm(callee.name), ordered),
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
      out.push({ term, proof: project(conjunction, conjunctionProjection(i)), depth, origin: "call-result" });
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
  private preCallProofs(e: ExprIR): Term[] {
    const callee = e.callee;
    const count = callee === undefined || callee.kind === "prelude" ? 0 : (this.signatureOf(callee)?.preconditions.length ?? 0);
    const site = e.sites.find((s) => s.kind === "pre-call");
    if (site === undefined) {
      if (count === 0) return [];
      throw new ElaborateFailure("the call has preconditions but no pre-call obligation");
    }
    const proof = this.proofs.get(site.id);
    if (proof === undefined) throw new ElaborateFailure("the pre-call obligation of this call was not certified");
    const out: Term[] = [];
    for (let i = 0; i < count; i += 1) {
      const path = conjunctionProjection(i);
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
    const siteProof = site === undefined ? undefined : this.proofs.get(site.id);
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
      const thenCtx = pushed(ctx, cond.thenBinder);
      const elseCtx = pushed(ctx, cond.elseBinder);
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
    const thenCtx = pushed(ctx, cond.thenBinder);
    const elseCtx = pushed(ctx, cond.elseBinder);
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
      const proof = this.proofs.get(site.id);
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
    this.proofs.set(site.id, solved.proof ?? K.tt);
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
      hypotheses = expandEquations(dedupeHyps([...hypsAt(hyps, depth), ...this.siteHyps(ctx, site, opts)]));
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

    const obligation: Obligation = {
      id: `${this.fn.name}#${site.id}`,
      kind: site.kind,
      span: site.span,
      context: ctx.binders.map((binder) => binder.type),
      hypotheses: hypotheses.map((hyp) => hyp.term),
      proofs: hypotheses.map((hyp) => hyp.proof),
      goal,
      atomNames: contextAtomNames(
        depth,
        ctx.binders.map((binder) => binder.surface ?? binder.name),
      ),
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
          `Z3 proved the ${site.kind} obligation \`${site.text}\` but no kernel certificate was ` +
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
    const list = expandEquations(dedupeHyps(hypsAt(hyps, depth)));
    for (const hyp of list) {
      if (sameTerm(hyp.term, goal)) return hyp.proof;
    }
    this.auxCount += 1;
    const obligation: Obligation = {
      id: `${this.fn.name}#aux${this.auxCount}`,
      kind,
      span,
      context: ctx.binders.map((binder) => binder.type),
      hypotheses: list.map((hyp) => hyp.term),
      proofs: list.map((hyp) => hyp.proof),
      goal,
      atomNames: contextAtomNames(
        depth,
        ctx.binders.map((binder) => binder.surface ?? binder.name),
      ),
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
          const inner = pushed(ctx, stmt.binder);
          const rest = this.elabStmts(inner, hypsAt(hyps, depth + 1), stmts.slice(i + 1));
          return K.letTerm(stmt.binder.name, stmt.binder.type, value.term, rest);
        }
        case "return":
          return this.elabReturn(ctx, hyps, stmt);
        case "if":
          return this.elabIf(ctx, hyps, stmt);
        case "switch":
          return this.elabSwitch(ctx, hyps, stmt);
        case "assign":
        case "loop":
        case "continue":
          this.internal(
            stmt.span,
            `\`${this.fn.name}\` uses ${stmt.kind === "loop" ? "a loop" : "a loop-carried assignment"}, ` +
              `and loop elaboration is not implemented yet (milestone 7 part B)`,
          );
          return K.tt;
      }
    }
    this.internal(this.fn.span, `not every path through \`${this.fn.name}\` ends in a \`return\``);
    return K.tt;
  }

  /** Certify everything the expression needs, then build its term and collect its facts. */
  private elabExpr(ctx: Ctx, hyps: readonly Hyp[], e: ExprIR): { term: Term; facts: Hyp[] } {
    const opts = this.optionsFor();
    const facts = this.withHyps(hyps, () => this.prepare(ctx, hyps, e, opts));
    const term = this.withHyps([...hyps, ...facts], () => exprTerm(ctx, e, opts));
    return { term, facts };
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
      const thenTerm = this.elabReturnValue(
        pushed(ctx, cond.thenBinder),
        [
          ...hypsAt(base, depth + 1),
          { term: shiftTerm(K.Le(a, b), 1), proof: K.varTerm(0), depth: depth + 1, origin: "condition" },
        ],
        cond.thenExpr,
        site,
      );
      const elseTerm = this.elabReturnValue(
        pushed(ctx, cond.elseBinder),
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
    const bound = this.bindReturnValue(ctx, hyps, valueExpr, value.term, value.facts);
    const proof = this.withHyps(bound.hyps, () =>
      this.certifyPost(bound.ctx, bound.hyps, site, bound.surface),
    );
    return bound.wrap(this.packResult(bound.ctx, bound.surface, proof, valueExpr));
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
    const extra = ctx.binders.length - this.fn.signature.binders.length;
    const sigmaType = shiftTerm(this.fn.signature.result.term, extra);
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
    const thenCtx = pushed(ctx, cond.thenBinder);
    const elseCtx = pushed(ctx, cond.elseBinder);
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
    return shiftTerm(this.fn.signature.result.term, ctx.binders.length - this.fn.signature.binders.length);
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
      let inner = pushed(ctx, branch.binder);
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
