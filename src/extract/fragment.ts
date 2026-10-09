/**
 * Fragment checking, name resolution, type mapping and obligation sites (specification 6.3).
 *
 * This module produces the typed IR that milestone 7 elaborates.  It never builds a *body*
 * term; what it produces is
 *
 *   - a kernel **signature type** per verified function (`FunctionIR.signature.type`),
 *   - a **statement IR** with loops already lowered to local `fixWf` functions (`ssa.ts`),
 *   - **obligation sites** (`ObligationSite`): kind, span, binder context, hypotheses and
 *     goal, with every implicit fact (parameter `InRange`, vector lengths and bounds,
 *     narrowing hypotheses, division lemmas, guarded-element facts) represented explicitly.
 *
 * Conventions every consumer relies on (see `docs/EXTRACT_NOTES.md`):
 *
 *  1. **Binders, not names.**  IR nodes refer to variables through `Slot`s holding `Binder`
 *     records.  A site lists the binders in scope, outermost first; a binder's de Bruijn
 *     index is `binders.length - 1 - position`.  `Binder.type` is a kernel term in the
 *     context of the *preceding* binders only (`shiftTerm` moves it under extra binders).
 *  2. **Propositions are `ExprIR`s of type `boolean`.**  `exprTerm(ctx, prop)` turns one into
 *     the kernel `Term`.  A goal mentioning `result` needs `{ result }`; a goal mentioning an
 *     index/slice/append term needs that site's proof in `{ proofs }` (milestone 6 only needs
 *     the term's shape, where proof arguments are irrelevant; milestone 7 supplies them).
 *
 * All diagnostics are reported, deterministically sorted; nothing inside an annotated
 * function throws.  `ExtractError` is thrown only by the *term builders*, for an IR node the
 * fragment does not give a kernel term (for example a bare union tag test outside a split).
 */
import { type Diagnostic, type DiagnosticKind, type Span, sortDiagnostics, spanFromOffsets } from "../diagnostics";
import * as K from "../kernel/index";
import type { ExternalDecl, Mk, Term } from "../kernel/index";
import type * as A from "../syntax/ast";
import type { JSDocTag } from "../syntax/jsdoc";
import { tagsNamed, tagSourceOffset } from "../syntax/jsdoc";
import { lex, type Token } from "../syntax/lexer";
import { parseFile } from "../syntax/parser";
import { lookupMathBuiltin, type MathBuiltin } from "./prelude";
import { SpecResolver, externalDeclFor, specAlias, specFunction } from "./specs";
import {
  envEmpty,
  envLookup,
  envWith,
  lowerLoop,
  type Continuation,
  type EnvVar,
  type FnEnv,
  type LoopHost,
} from "./ssa";

/** Thrown by the term builders when the IR does not determine a kernel term. */
export class ExtractError extends Error {}

// ===========================================================================
// 1. The IR
// ===========================================================================

export type TypeKind = "int" | "boolean" | "vec" | "generic" | "union";

export interface TypeIR {
  readonly kind: TypeKind;
  readonly span: Span;
  /** `vec` only. */
  readonly elem?: TypeIR;
  /** `generic` only: the surface name of the type parameter. */
  readonly typeParam?: string;
  /** `union` only. */
  readonly union?: UnionIR;
}

export interface FieldIR {
  readonly name: string;
  readonly type: TypeIR;
  readonly span: Span;
  /** Projection path from the variant record to the value: `[0]` = fst, `[1,0]` = fst of snd. */
  readonly path: readonly number[];
  /** For a `number` field: the projection path to its `InRange` proof component. */
  readonly inRangePath?: readonly number[];
}

export interface VariantIR {
  /** The name of a named variant (`| Square`), or null for an inline object type. */
  readonly name: string | null;
  /** The shared string-literal discriminant value. */
  readonly tag: string;
  /** Declaration order, from 0. */
  readonly index: number;
  /** The non-discriminant fields, in declaration order. */
  readonly fields: readonly FieldIR[];
  /** Nested `Sigma` record of the fields (a `number` field contributes value and proof). */
  readonly recordType: Term;
  readonly span: Span;
}

export interface UnionIR {
  readonly name: string;
  readonly discriminant: string;
  readonly variants: readonly VariantIR[];
  /** Nested `Sum` of the variant records, in declaration order. */
  readonly sumType: Term;
  /** The file the alias was declared in. */
  readonly file: string;
  readonly span: Span;
}

export type BinderRole =
  | "type-param"
  | "param"
  | "in-range"
  | "vec-len"
  | "vec-elems"
  | "pre"
  | "hypothesis"
  | "payload"
  | "local"
  | "loop-state"
  | "loop-measure-nonneg"
  | "invariant"
  | "result";

export interface Binder {
  /** Unique within one `extractFile` call. */
  readonly id: number;
  /** Kernel name; synthesized binders get a readable prefix (`rx`, `n_a`, `v_square`, …). */
  readonly name: string;
  readonly role: BinderRole;
  /** Kernel type, in the context of the preceding binders only. */
  readonly type: Term;
  /** Surface name this binder was introduced for, when there is one. */
  readonly surface?: string;
  readonly span?: Span;
}

/** Where the current value of a name lives. */
export type Slot =
  | { readonly kind: "binder"; readonly binder: Binder }
  /** A component of a loop's carried-state tuple. */
  | {
      readonly kind: "state";
      readonly state: Binder;
      readonly path: readonly number[];
      /** The carried variable's surface name, for rendering. */
      readonly name?: string;
    }
  /** The payload of a union variant, in a branch narrowed to exactly that variant. */
  | { readonly kind: "payload"; readonly union: UnionIR; readonly variant: VariantIR; readonly payload: Binder }
  /** `result`, inside a `@post`. */
  | { readonly kind: "result" };

export type FactOrigin =
  | "param-in-range"
  | "vec-bounds"
  | "pre"
  | "condition"
  | "invariant"
  | "tag-test"
  | "element-range"
  | "division-spec"
  | "call-result"
  | "measure"
  | "field-in-range";

export interface FactIR {
  /** The proposition, as a `boolean`-typed `ExprIR`. */
  readonly prop: ExprIR;
  readonly origin: FactOrigin;
  /** The binder holding the proof, when the fact is a hypothesis in scope. */
  readonly binder?: Binder;
  /** Short rendering, for diagnostics. */
  readonly text?: string;
}

export interface Narrowing {
  /** The narrowed subject; always a `binder` or `payload` slot. */
  readonly subject: Slot;
  readonly union: UnionIR;
  /** The single remaining variant, or null when several are still possible. */
  readonly variant: VariantIR | null;
  /** Discriminant tags still possible, in declaration order. */
  readonly allowed: readonly string[];
  /** The payload binder for `variant`, when there is one. */
  readonly payload: Binder | null;
}

export type ExprKind =
  | "int"
  | "bool"
  | "string"
  /** The trivially true proposition `Unit`. */
  | "true"
  | "ref"
  | "field"
  | "length"
  | "neg"
  | "not"
  | "add"
  | "sub"
  | "mul"
  | "lt"
  | "le"
  | "gt"
  | "ge"
  | "eq"
  | "neq"
  | "and"
  | "or"
  | "cond"
  | "inRange"
  | "call"
  | "projection"
  | "index"
  | "slice"
  | "append"
  | "object"
  | "tagTest";

export interface TagTestIR {
  readonly subject: Slot;
  readonly union: UnionIR;
  readonly variant: VariantIR;
  readonly positive: boolean;
}

export interface CondIR {
  readonly expr: ExprIR;
  /** The binder holding the condition in each branch. */
  readonly thenBinder: Binder;
  readonly elseBinder: Binder;
  /** The proposition bound in the then branch (its integer complement is bound otherwise). */
  readonly prop: ExprIR;
  readonly thenNarrowings: readonly Narrowing[];
  readonly elseNarrowings: readonly Narrowing[];
  readonly tagTest?: TagTestIR;
  /** For a condition *expression* (a ternary): its two branches. */
  readonly thenExpr?: ExprIR;
  readonly elseExpr?: ExprIR;
}

export interface ResultLayout {
  readonly shape: ResultShape;
  /** `fst`/`snd` path to the surface value of a call result. */
  readonly valuePath: readonly number[];
  readonly inRangePath?: readonly number[];
  readonly lengthPath?: readonly number[];
  readonly vecPath?: readonly number[];
  readonly postPath?: readonly number[];
}

export type ResultShape = "int" | "vec" | "generic" | "union";

export interface ExprIR {
  readonly kind: ExprKind;
  readonly span: Span;
  readonly type: TypeIR;
  readonly args: readonly ExprIR[];
  readonly literal?: bigint | boolean | string;
  readonly slot?: Slot;
  readonly union?: UnionIR;
  readonly variant?: VariantIR;
  readonly field?: FieldIR;
  readonly callee?: CalleeIR;
  /** For vec-typed expressions: the expression denoting the vector's length. */
  readonly vecLength?: ExprIR;
  /** Conditions carry their branch structure. */
  readonly cond?: CondIR;
  /** `and`/`or`: the binder that holds the left operand inside the right one. */
  readonly rightBinder?: Binder;
  /** `projection`: path of `fst`/`snd` steps (0 = fst, 1 = snd). */
  readonly projPath?: readonly number[];
  /** `call`: where each part of the packed result lives. */
  readonly layout?: ResultLayout;
  /** `index`/`slice`/`append`: the site whose proof this term needs. */
  readonly siteId?: number;
  readonly sites: readonly ObligationSite[];
  readonly facts: readonly FactIR[];
}

export type ObligationKind =
  | "post"
  | "pre-call"
  | "index"
  | "slice"
  | "append-length"
  | "range"
  | "measure-nonneg"
  | "measure-decrease"
  | "invariant-init"
  | "invariant-preserve";

export interface ObligationSite {
  readonly id: number;
  readonly kind: ObligationKind;
  readonly span: Span;
  /** The binders in scope, outermost first. */
  readonly context: readonly Binder[];
  /** The propositions assumed at this site. */
  readonly hypotheses: readonly FactIR[];
  /** The proposition to prove. */
  readonly goal: ExprIR;
  /** For `post`: the returned expression, which `result` refers to. */
  readonly resultValue?: ExprIR;
  /** A short rendering of the goal, for diagnostics. */
  readonly text: string;
}

export interface ParamIR {
  readonly name: string;
  readonly binder: Binder;
  readonly type: TypeIR;
  /** Synthetic binders the parameter introduced (length, element guard, `InRange` proof). */
  readonly extra: readonly Binder[];
  readonly span: Span;
}

export interface ResultIR {
  readonly shape: ResultShape;
  /** The surface return type. */
  readonly type: TypeIR;
  /** The binder for the result value (`r : Int`, `m : Int`), when the shape has one. */
  readonly binder?: Binder;
  /** The kernel codomain, in the context of the signature binders. */
  readonly term: Term;
  /** Postcondition facts, checked with `result` bound. */
  readonly posts: readonly FactIR[];
  readonly layout: ResultLayout;
}

export interface CalleeIR {
  readonly kind: "local" | "self" | "imported" | "prelude";
  /** Surface name as written at the call. */
  readonly name: string;
  /** For `local`/`self`; null while the function is still being built. */
  readonly fn?: FunctionIR | null;
  /** For `imported`. */
  readonly imported?: ImportedSpec;
  /** For `prelude`. */
  readonly builtin?: MathBuiltin;
}

export interface ImportedSpec {
  readonly name: string;
  readonly file: string;
  readonly hash: string;
  readonly signature: SignatureIR;
  readonly decl: ExternalDecl;
}

/** A function's kernel signature, shared by local calls, recursive calls and externals. */
export interface SignatureIR {
  /** The full binder telescope, outermost first. */
  readonly binders: readonly Binder[];
  /** Precondition facts, in tag order. */
  readonly preconditions: readonly FactIR[];
  readonly result: ResultIR;
  /** The closed kernel type of the function. */
  readonly type: Term;
}

export interface LoopVarIR {
  /** Surface name of the carried variable. */
  readonly name: string;
  /** Path from the loop's state binder to this component. */
  readonly path: readonly number[];
  readonly type: TypeIR;
  /** Its value before the loop, in the enclosing context. */
  readonly initial: ExprIR;
}

export interface LoopIR {
  readonly id: number;
  /** Kernel name of the local recursive function, e.g. `loop0`. */
  readonly name: string;
  readonly span: Span;
  /** `A`: the carried-state tuple type. */
  readonly stateType: Term;
  readonly state: Binder;
  readonly carried: readonly LoopVarIR[];
  /** The `@invariant` conjunction, in the body scope. */
  readonly invariant: ExprIR;
  /** The invariant as an `A -> Type 0` predicate. */
  readonly invariantType: Term;
  /** The `@decreases` measure, in the body scope. */
  readonly measure: ExprIR;
  /** The `@decreases` measure as an `A -> Int` function. */
  readonly measureType: Term;
  /** `hinv : Invariant state`, available in the body. */
  readonly invariantBinder: Binder;
  /** `B = fun _ => Invariant s -> Result`. */
  readonly resultMotive: Term;
  /** The function's result type (the `Result` of the motive). */
  readonly resultType: Term;
  /** The loop condition. */
  test: CondIR;
  /** The then branch: body statements ending in `continue` or `return`. */
  body: StmtIR[];
  /** The else branch: the rest of the function, ending in `return`. */
  rest: StmtIR[];
  /** `invariant-init` and `measure-nonneg`, in the enclosing context. */
  initSites: ObligationSite[];
}

export type StmtIR =
  | {
      readonly kind: "local";
      readonly binder: Binder;
      readonly value: ExprIR;
      readonly mutable: boolean;
      readonly span: Span;
    }
  | { readonly kind: "assign"; readonly target: Slot; readonly value: ExprIR; readonly span: Span }
  | {
      readonly kind: "if";
      readonly cond: CondIR;
      readonly then: readonly StmtIR[];
      readonly otherwise: readonly StmtIR[];
      readonly span: Span;
    }
  | { readonly kind: "return"; readonly value: ExprIR; readonly site: ObligationSite; readonly span: Span }
  | {
      readonly kind: "switch";
      readonly subject: Slot;
      /**
       * The union being discriminated.  Milestone 7 needs it to build the nested `Sum`
       * case split (`sumAfter`/`sumInjection` are defined on the `UnionIR`, not on a case).
       */
      readonly union: UnionIR;
      readonly cases: readonly SwitchCaseIR[];
      readonly span: Span;
    }
  | {
      readonly kind: "continue";
      readonly loop: LoopIR;
      readonly values: readonly { readonly variable: LoopVarIR; readonly value: ExprIR }[];
      readonly sites: readonly ObligationSite[];
      readonly span: Span;
    }
  | { readonly kind: "loop"; readonly loop: LoopIR; readonly span: Span }
  | { readonly kind: "expr"; readonly expr: ExprIR; readonly span: Span }
  | { readonly kind: "nop"; readonly span: Span };

export interface SwitchCaseIR {
  /** The discriminant string, or null for `default`. */
  readonly tag: string | null;
  readonly variant: VariantIR | null;
  readonly payload: Binder | null;
  readonly body: readonly StmtIR[];
  readonly span: Span;
}

export interface FunctionIR {
  readonly name: string;
  readonly span: Span;
  readonly nameSpan: Span;
  readonly exported: boolean;
  readonly typeParams: readonly Binder[];
  readonly params: readonly ParamIR[];
  readonly signature: SignatureIR;
  /** `@decreases` on the function, in the parameter context. */
  readonly measure?: ExprIR;
  readonly recursive: boolean;
  readonly body: readonly StmtIR[];
  readonly loops: readonly LoopIR[];
  /** Every obligation site in the function, in source order. */
  readonly sites: readonly ObligationSite[];
  /** Imported specs this function used, in first-use order. */
  readonly imports: readonly ImportedSpec[];
}

export interface FileIR {
  readonly path: string;
  readonly source: string;
  readonly functions: readonly FunctionIR[];
  readonly unions: readonly UnionIR[];
  /** Content hashes of imported files whose specs were used, keyed by absolute path. */
  readonly importedHashes: ReadonlyMap<string, string>;
  readonly diagnostics: readonly Diagnostic[];
}

// ===========================================================================
// 2. Contexts and term builders
// ===========================================================================

/** Unique binder and site ids inside one extraction run. */
export class Ids {
  private next = 0;

  fresh(): number {
    return (this.next += 1);
  }
}

/** The typing context: binders in scope (outermost first), facts, narrowings, id source. */
export interface Ctx {
  readonly binders: readonly Binder[];
  readonly facts: readonly FactIR[];
  readonly narrowings: readonly Narrowing[];
  readonly ids: Ids;
}

export function deBruijnIndex(ctx: Ctx, binder: Binder): number {
  for (let i = ctx.binders.length - 1; i >= 0; i -= 1) {
    if (ctx.binders[i]!.id === binder.id) return ctx.binders.length - 1 - i;
  }
  throw new ExtractError(`binder ${binder.name}#${binder.id} is not in scope`);
}

function ctxLookup(ctx: Ctx, name: string): Binder | undefined {
  for (let i = ctx.binders.length - 1; i >= 0; i -= 1) {
    const binder = ctx.binders[i]!;
    if (binder.surface === name) return binder;
  }
  return undefined;
}

export function ctxLookupRole(ctx: Ctx, name: string, role: BinderRole): Binder | undefined {
  for (let i = ctx.binders.length - 1; i >= 0; i -= 1) {
    const binder = ctx.binders[i]!;
    if (binder.surface === name && binder.role === role) return binder;
  }
  return undefined;
}

export function bind(
  ctx: Ctx,
  name: string,
  type: Term,
  role: BinderRole,
  surface?: string,
  span?: Span,
): { ctx: Ctx; binder: Binder } {
  const binder: Binder = { id: ctx.ids.fresh(), name, role, type, surface, span };
  return { ctx: { ...ctx, binders: [...ctx.binders, binder] }, binder };
}

export function withFact(ctx: Ctx, fact: FactIR): Ctx {
  return { ...ctx, facts: [...ctx.facts, fact] };
}

export function withNarrowings(ctx: Ctx, narrowings: readonly Narrowing[]): Ctx {
  return narrowings.length === 0 ? ctx : { ...ctx, narrowings: [...ctx.narrowings, ...narrowings] };
}

function sameSlot(a: Slot, b: Slot): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "binder" && b.kind === "binder") return a.binder.id === b.binder.id;
  if (a.kind === "state" && b.kind === "state") {
    return a.state.id === b.state.id && a.path.join(",") === b.path.join(",");
  }
  if (a.kind === "payload" && b.kind === "payload") return a.payload.id === b.payload.id;
  return a.kind === "result" && b.kind === "result";
}

export function slotText(slot: Slot): string {
  switch (slot.kind) {
    case "binder":
      return slot.binder.surface ?? slot.binder.name;
    case "state":
      return slot.name ?? slot.state.name;
    case "payload":
      return slot.payload.surface ?? slot.payload.name;
    case "result":
      return "result";
  }
}

export function narrowingOf(ctx: Ctx, slot: Slot): Narrowing | undefined {
  for (let i = ctx.narrowings.length - 1; i >= 0; i -= 1) {
    const narrowing = ctx.narrowings[i]!;
    if (sameSlot(narrowing.subject, slot)) return narrowing;
  }
  return undefined;
}

export interface TermOptions {
  /** The term `result` refers to, for a `@post` goal. */
  readonly result?: Term;
  /** Proof terms for obligation sites, keyed by site id (milestone 7 fills these in). */
  readonly proofs?: ReadonlyMap<number, Term>;
  /**
   * Milestone 7 hook: a node whose kernel term needs more than this module can build from
   * the IR alone.  `call` needs the callee's whole binder telescope (argument `InRange`
   * proofs, bounds for the vector arguments, the callee's preconditions) and `append` needs
   * one `Le (prefix + part) 4294967295` proof per spread part; the elaborator supplies both.
   * Returning `undefined` falls through to the default (the prelude's `Math.*` calls, whose
   * definitions this module builds itself, are never overridden).
   */
  readonly override?: (ctx: Ctx, e: ExprIR, opts: TermOptions) => Term | undefined;
}

/** The override hook, when the options carry one. */
function overrideTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term | undefined {
  return opts?.override?.(ctx, e, opts);
}

/** `fst`/`snd` path: `[0]` is `fst`, `[1,0]` is `fst` of `snd`, `[]` is the value itself. */
export function project(term: Term, path: readonly number[]): Term {
  let out = term;
  for (const step of path) out = step === 0 ? K.fst(out) : K.snd(out);
  return out;
}

function proofFor(e: ExprIR, opts: TermOptions | undefined): Term {
  const id = e.siteId;
  const proof = id === undefined ? undefined : opts?.proofs?.get(id);
  if (proof === undefined) {
    throw new ExtractError(
      `the term for \`${e.kind}\` needs the proof of obligation site #${id ?? "?"}; pass it in TermOptions.proofs`,
    );
  }
  return proof;
}

function applyPath(term: Term, path: readonly number[] | undefined): Term {
  return path === undefined || path.length === 0 ? term : project(term, path);
}

/** The kernel term a slot denotes, in the context `ctx`. */
export function slotTerm(ctx: Ctx, slot: Slot, opts?: TermOptions): Term {
  switch (slot.kind) {
    case "binder":
      return { tag: "Var", index: deBruijnIndex(ctx, slot.binder) };
    case "state":
      return project({ tag: "Var", index: deBruijnIndex(ctx, slot.state) }, slot.path);
    case "payload":
      return sumInjection(slot.union, slot.variant, {
        tag: "Var",
        index: deBruijnIndex(ctx, slot.payload),
      });
    case "result": {
      if (opts?.result === undefined) {
        throw new ExtractError("`result` has no term here; pass TermOptions.result");
      }
      return opts.result;
    }
  }
}

// --------------------------------------------------------------------------
// Union encodings
// --------------------------------------------------------------------------

/** `T(i+1)`: the sum of the variants after index `i`. */
export function sumAfter(union: UnionIR, i: number): Term {
  let out = union.variants[union.variants.length - 1]!.recordType;
  for (let j = union.variants.length - 2; j > i; j -= 1) out = K.Sum(union.variants[j]!.recordType, out);
  return out;
}

/** `inl`/`inr` chain injecting a variant record into the nested `Sum`. */
export function sumInjection(union: UnionIR, variant: VariantIR, payload: Term): Term {
  return injectAt(0, payload);

  function injectAt(i: number, value: Term): Term {
    if (i === union.variants.length - 1) return value;
    const left = union.variants[i]!.recordType;
    const right = sumAfter(union, i);
    if (i === variant.index) return K.Inl(left, right, value);
    return K.Inr(left, right, injectAt(i + 1, value));
  }
}

/**
 * "The subject is (or is not) the k-th variant", as a `Type 0` proposition:
 * `case s of inl v => … | inr w => …`, recursing through the nested `Sum`.  Sound as a goal,
 * not just as a branch hypothesis.
 */
export function tagTestTerm(union: UnionIR, variantIndex: number, positive: boolean, subject: Term): Term {
  return testAt(0, subject);

  function testAt(i: number, scrutinee: Term): Term {
    if (i === union.variants.length - 1) {
      return (i === variantIndex) === positive ? K.Unit : K.Empty;
    }
    const left = union.variants[i]!.recordType;
    const right = sumAfter(union, i);
    const motive = K.lam("_", K.Sum(left, right), K.sort(0));
    const onLeft = K.lam("_", left, (i === variantIndex) === positive ? K.Unit : K.Empty);
    const onRight = K.lam("_", right, testAt(i + 1, K.varTerm(0)));
    return K.SumCase(1, left, right, motive, onLeft, onRight, scrutinee);
  }
}

/** The kernel element type of a `vec`. */
export function elemKernelType(ctx: Ctx, type: TypeIR): Term {
  switch (type.kind) {
    case "int":
      return K.Int;
    case "generic": {
      const binder = ctxLookupRole(ctx, type.typeParam!, "type-param");
      if (binder === undefined) throw new ExtractError(`unbound type parameter ${type.typeParam}`);
      return { tag: "Var", index: deBruijnIndex(ctx, binder) };
    }
    case "union":
      return type.union!.sumType;
    case "vec":
      throw new ExtractError("nested vectors are not in the fragment");
    case "boolean":
      throw new ExtractError("`boolean` is only allowed as the type of a condition");
  }
}

/** The kernel type of a value of `type`, for shapes that do not need a length. */
export function valueKernelType(ctx: Ctx, type: TypeIR): Term {
  switch (type.kind) {
    case "int":
      return K.Int;
    case "union":
      return type.union!.sumType;
    case "generic":
      return elemKernelType(ctx, type);
    case "vec":
      throw new ExtractError("a vector type needs its length");
    case "boolean":
      throw new ExtractError("`boolean` is only allowed as the type of a condition");
  }
}

/** `And p1 (And p2 … pn)`; `Unit` when the list is empty. */
export function andAll(terms: readonly Term[]): Term {
  if (terms.length === 0) return K.Unit;
  let out = terms[terms.length - 1]!;
  for (let i = terms.length - 2; i >= 0; i -= 1) out = K.And(terms[i]!, out);
  return out;
}

/** The integer complement of a comparison, as the `ifLe`/case other-branch sees it. */
export function negateCondition(cond: ExprIR): ExprIR {
  const base = { span: cond.span, type: cond.type, args: cond.args, sites: [], facts: [] } as const;
  switch (cond.kind) {
    case "lt":
      return { kind: "ge", ...base };
    case "le":
      return { kind: "gt", ...base };
    case "gt":
      return { kind: "le", ...base };
    case "ge":
      return { kind: "lt", ...base };
    case "eq":
      return { kind: "neq", ...base };
    case "neq":
      return { kind: "eq", ...base };
    default:
      return { kind: "true", span: cond.span, type: cond.type, args: [], sites: [], facts: [] };
  }
}

export function isComparison(e: ExprIR): boolean {
  return (
    e.kind === "lt" || e.kind === "le" || e.kind === "gt" || e.kind === "ge" || e.kind === "eq" || e.kind === "neq"
  );
}

/** The kernel proposition a `boolean`-typed `ExprIR` denotes. */
export function exprTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  switch (e.kind) {
    case "int":
      return K.intLit(e.literal as bigint);
    case "true":
      return K.Unit;
    case "ref":
      return slotTerm(ctx, e.slot!, opts);
    case "field": {
      // Inside the narrowed branch the payload is a bound variable (`SumCase`'s lambda);
      // projecting the *injection* would be ill-typed, so project the variable itself.
      const slot = e.slot!;
      const base =
        slot.kind === "payload"
          ? { tag: "Var", index: deBruijnIndex(ctx, slot.payload) } as Term
          : slotTerm(ctx, slot, opts);
      return project(base, e.field!.path);
    }
    case "length":
      if (e.vecLength === undefined) throw new ExtractError("a vector length was not resolved");
      return exprTerm(ctx, e.vecLength, opts);
    case "neg":
      return K.Neg(exprTerm(ctx, e.args[0]!, opts));
    case "not":
      return K.Not(exprTerm(ctx, e.args[0]!, opts));
    case "add":
      return K.Add(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "sub":
      return K.Sub(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "mul":
      return K.MulConst(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "lt":
      return K.Lt(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "le":
      return K.Le(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "gt":
      return K.Lt(exprTerm(ctx, e.args[1]!, opts), exprTerm(ctx, e.args[0]!, opts));
    case "ge":
      return K.Le(exprTerm(ctx, e.args[1]!, opts), exprTerm(ctx, e.args[0]!, opts));
    case "eq":
      return K.Eq(K.Int, exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "neq":
      return K.Not(K.Eq(K.Int, exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts)));
    case "and":
      // `And A B` keeps both operands at the same depth: the binder `rightBinder` records the
      // assumption the *right* operand may use when it is a hypothesis, but the kernel term
      // needs no lambda for it.
      return K.And(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "or":
      return K.Sum(exprTerm(ctx, e.args[0]!, opts), exprTerm(ctx, e.args[1]!, opts));
    case "cond":
      return conditionTerm(ctx, e, opts);
    case "inRange":
      return K.InRange(exprTerm(ctx, e.args[0]!, opts));
    case "call":
      return applyPath(callApplication(ctx, e, opts), e.layout?.valuePath);
    case "projection":
      return applyPath(rawTerm(ctx, e.args[0]!, opts), e.projPath);
    case "index": {
      const vec = e.args[0]!;
      return K.Get(
        elemKernelType(ctx, vec.type.elem!),
        exprTerm(ctx, vec.vecLength!, opts),
        exprTerm(ctx, vec, opts),
        exprTerm(ctx, e.args[1]!, opts),
        proofFor(e, opts),
      );
    }
    case "slice": {
      const vec = e.args[0]!;
      return K.Slice(
        elemKernelType(ctx, vec.type.elem!),
        exprTerm(ctx, vec.vecLength!, opts),
        exprTerm(ctx, vec, opts),
        exprTerm(ctx, e.args[1]!, opts),
        exprTerm(ctx, e.args[2]!, opts),
        proofFor(e, opts),
      );
    }
    case "append": {
      // The elaborator supplies the whole chain through the override hook: each step needs a
      // `Le (prefix + part) 4294967295` proof, and only the last one is the site's.  Without
      // the hook only a single spread can be built faithfully (the site's proof is about the
      // whole concatenation), which is what this fallback does.  There is no empty vector
      // value in the kernel, so the first part is the seed.
      const custom = overrideTerm(ctx, e, opts);
      if (custom !== undefined) return custom;
      const elem = elemKernelType(ctx, e.type.elem!);
      const proof = proofFor(e, opts);
      const first = e.args[0];
      if (first === undefined) throw new ExtractError("an array literal needs at least one spread part");
      let length: Term = exprTerm(ctx, first.vecLength!, opts);
      let vec: Term = exprTerm(ctx, first, opts);
      for (let i = 1; i < e.args.length; i += 1) {
        const part = e.args[i]!;
        const partLen = exprTerm(ctx, part.vecLength!, opts);
        vec = K.Append(elem, length, partLen, vec, exprTerm(ctx, part, opts), proof);
        length = K.Add(length, partLen);
      }
      return vec;
    }
    case "tagTest":
      return tagTestTerm(e.union!, e.variant!.index, e.literal === true, slotTerm(ctx, e.slot!, opts));
    case "object":
      return objectTerm(ctx, e, opts);
    case "string":
    case "bool":
      throw new ExtractError(`\`${e.kind}\` is not a kernel term`);
  }
}

/**
 * `exprTerm`, but a node whose kernel term needs an obligation proof (an `index`, a `slice`,
 * an `append`) falls back to `Unit` when the proof is not available yet.  Hypothesis binder
 * *types* are advisory: milestone 7 rebuilds them together with the proofs it certifies.
 */
export function safePropTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  try {
    return exprTerm(ctx, e, opts);
  } catch {
    return K.Unit;
  }
}

/**
 * The term of a node whose packed result has to be kept packed: a `projection` node picks a
 * component out of a call's `Sigma` result, so the call must not be unpacked here.  Anything
 * else (a vector argument of `get`/`slice`/`append`, a spread part) is an ordinary value
 * term, which is what `exprTerm` builds.
 */
function rawTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  if (e.kind === "call") return callApplication(ctx, e, opts);
  return exprTerm(ctx, e, opts);
}

function callApplication(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  const callee = e.callee!;
  if (callee.kind === "prelude") return callee.builtin!.build(e.args.map((arg) => exprTerm(ctx, arg, opts)));
  const custom = overrideTerm(ctx, e, opts);
  if (custom !== undefined) return custom;
  return K.appMany(
    K.constTerm(callee.name),
    e.args.map((arg) => exprTerm(ctx, arg, opts)),
  );
}

/** A constructed union value: the nested `Sigma` record injected into the nested `Sum`. */
function objectTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  const variant = e.variant!;
  let record: Term = K.tt;
  for (let i = variant.fields.length - 1; i >= 0; i -= 1) {
    const field = variant.fields[i]!;
    const value = exprTerm(ctx, e.args[i]!, opts);
    record = K.pair(recordPrefixType(variant, i), value, record);
  }
  return sumInjection(e.union!, variant, record);
}

/** `Sigma (f_i : T_i). …` for the record starting at field `i` (closed, so builder-made). */
function recordPrefixType(variant: VariantIR, i: number): Term {
  const components: { name: string; type: Mk }[] = [];
  for (let j = i; j < variant.fields.length; j += 1) {
    const field = variant.fields[j]!;
    components.push({ name: field.name, type: typeMkOf(field.type) });
    if (field.type.kind === "int") {
      components.push({
        name: "_",
        type: (scope) => K.InRange(K.varTerm(scope.index(field.name))),
      });
    }
  }
  let out: Mk = () => K.Unit;
  for (let j = components.length - 1; j >= 0; j -= 1) {
    const inner = out;
    const name = components[j]!.name;
    const type = components[j]!.type;
    out = (scope) => K.sigma(name, type(scope), inner(scope.bind(name)));
  }
  return K.mk(out);
}

function conditionTerm(ctx: Ctx, e: ExprIR, opts?: TermOptions): Term {
  const cond = e.cond;
  if (cond === undefined) throw new ExtractError("a `cond` node without its condition");
  if (cond.tagTest !== undefined) return caseSplitTerm(ctx, cond, opts);
  const lhs = exprTerm(ctx, cond.expr.args[0]!, opts);
  const rhs = exprTerm(ctx, cond.expr.args[1]!, opts);
  return ifLeTerm(ctx, cond, lhs, rhs, opts);
}

/** `ifLe`'s two integer arguments for each comparison. */
function ifLeOperands(cond: ExprIR, lhs: Term, rhs: Term): [Term, Term] {
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

function ifLeTerm(ctx: Ctx, cond: CondIR, lhs: Term, rhs: Term, opts?: TermOptions): Term {
  const [a, b] = ifLeOperands(cond.expr, lhs, rhs);
  const branchIsProp = cond.thenExpr!.type.kind === "boolean";
  const level = branchIsProp ? 1 : 0;
  const motive = branchIsProp ? K.sort(0) : K.Int;
  const thenCtx: Ctx = { ...ctx, binders: [...ctx.binders, cond.thenBinder] };
  const elseCtx: Ctx = { ...ctx, binders: [...ctx.binders, cond.elseBinder] };
  return K.IfLe(
    level,
    motive,
    a,
    b,
    K.lam(cond.thenBinder.name, K.Le(a, b), exprTerm(thenCtx, cond.thenExpr!, opts)),
    K.lam(cond.elseBinder.name, K.Lt(b, a), exprTerm(elseCtx, cond.elseExpr!, opts)),
  );
}

/**
 * A ternary/condition on a union discriminant, as a case split.  Only two-variant unions are
 * split here; a wider union is rejected by the fragment checker (`ssa.ts` never sees one).
 */
function caseSplitTerm(ctx: Ctx, cond: CondIR, opts?: TermOptions): Term {
  const test = cond.tagTest!;
  const union = test.union;
  const n = union.variants.length;
  if (n !== 2) throw new ExtractError(`cannot split a ${n}-variant union in a condition`);
  const left = union.variants[0]!;
  const right = union.variants[1]!;
  const scrutinee = slotTerm(ctx, test.subject, opts);
  const thenCtx: Ctx = { ...ctx, binders: [...ctx.binders, cond.thenBinder] };
  const elseCtx: Ctx = { ...ctx, binders: [...ctx.binders, cond.elseBinder] };
  const branchIsProp = cond.thenExpr!.type.kind === "boolean";
  const level = branchIsProp ? 1 : 0;
  const motive = K.lam("_", union.sumType, branchIsProp ? K.sort(0) : K.Int);
  if (test.variant.index === 0 === test.positive) {
    return K.SumCase(
      level,
      left.recordType,
      right.recordType,
      motive,
      K.lam(cond.thenBinder.name, left.recordType, exprTerm(thenCtx, cond.thenExpr!, opts)),
      K.lam(cond.elseBinder.name, right.recordType, exprTerm(elseCtx, cond.elseExpr!, opts)),
      scrutinee,
    );
  }
  return K.SumCase(
    level,
    left.recordType,
    right.recordType,
    motive,
    K.lam(cond.elseBinder.name, left.recordType, exprTerm(elseCtx, cond.elseExpr!, opts)),
    K.lam(cond.thenBinder.name, right.recordType, exprTerm(thenCtx, cond.thenExpr!, opts)),
    scrutinee,
  );
}

/** The context a site's goal and hypotheses live in. */
export function ctxOfSite(site: ObligationSite, ids: Ids = new Ids()): Ctx {
  return { binders: site.context, facts: site.hypotheses, narrowings: [], ids };
}

/** The `Term` of a site's goal; `result` and proof terms come from `opts`. */
export function goalTerm(site: ObligationSite, opts?: TermOptions): Term {
  return exprTerm(ctxOfSite(site), site.goal, opts);
}


/** A short rendering of an expression, for diagnostics and tests. */
export function renderExpr(e: ExprIR): string {
  switch (e.kind) {
    case "int":
      return String(e.literal);
    case "bool":
      return e.literal === true ? "true" : "false";
    case "string":
      return JSON.stringify(e.literal);
    case "true":
      return "Unit";
    case "ref":
      return slotText(e.slot!);
    case "field":
      return `${renderExpr(e.args[0]!)}.${e.field!.name}`;
    case "length":
      return `${renderExpr(e.args[0]!)}.length`;
    case "neg":
      return `-${renderExpr(e.args[0]!)}`;
    case "not":
      return `!(${renderExpr(e.args[0]!)})`;
    case "add":
      return `(${renderExpr(e.args[0]!)} + ${renderExpr(e.args[1]!)})`;
    case "sub":
      return `(${renderExpr(e.args[0]!)} - ${renderExpr(e.args[1]!)})`;
    case "mul":
      return `(${renderExpr(e.args[0]!)} * ${renderExpr(e.args[1]!)})`;
    case "lt":
      return `(${renderExpr(e.args[0]!)} < ${renderExpr(e.args[1]!)})`;
    case "le":
      return `(${renderExpr(e.args[0]!)} <= ${renderExpr(e.args[1]!)})`;
    case "gt":
      return `(${renderExpr(e.args[0]!)} > ${renderExpr(e.args[1]!)})`;
    case "ge":
      return `(${renderExpr(e.args[0]!)} >= ${renderExpr(e.args[1]!)})`;
    case "eq":
      return `(${renderExpr(e.args[0]!)} === ${renderExpr(e.args[1]!)})`;
    case "neq":
      return `(${renderExpr(e.args[0]!)} !== ${renderExpr(e.args[1]!)})`;
    case "and":
      return `(${renderExpr(e.args[0]!)} && ${renderExpr(e.args[1]!)})`;
    case "or":
      return `(${renderExpr(e.args[0]!)} || ${renderExpr(e.args[1]!)})`;
    case "cond":
      return `(${renderExpr(e.cond!.expr)} ? ${renderExpr(e.cond!.thenExpr!)} : ${renderExpr(e.cond!.elseExpr!)})`;
    case "inRange":
      return `InRange(${renderExpr(e.args[0]!)})`;
    case "tagTest":
      return `${slotText(e.slot!)}.${e.union!.discriminant} === ${JSON.stringify(e.variant!.tag)}`;
    case "call":
      return `${e.callee?.name}(${e.args.map(renderExpr).join(", ")})`;
    case "projection":
      return `proj(${renderExpr(e.args[0]!)}, ${e.projPath!.join(".")})`;
    case "index":
      return `${renderExpr(e.args[0]!)}[${renderExpr(e.args[1]!)}]`;
    case "slice":
      return `${renderExpr(e.args[0]!)}.slice(${renderExpr(e.args[1]!)}, ${renderExpr(e.args[2]!)})`;
    case "append":
      return `[${e.args.map((a) => `...${renderExpr(a)}`).join(", ")}]`;
    case "object":
      return `{ ${e.variant!.tag} }`;
  }
}

// ===========================================================================
// 3. Spec expressions (parsed out of JSDoc tag text)
// ===========================================================================

/** The numeric value of an integer literal token (floats return `null`). */
function numericValue(token: Token): bigint | null {
  const info = token.numeric;
  if (info === undefined || info.isFloat) return null;
  const text = token.text.replace(/_/g, "");
  const body = info.isBigInt && text.endsWith("n") ? text.slice(0, -1) : text;
  try {
    return BigInt(body);
  } catch {
    return null;
  }
}

/**
 * A small recursive-descent parser for the spec-expression grammar (section 4.1), over the
 * tokens of one JSDoc tag.  It produces the same `A.Expr` nodes the body parser produces, so
 * that specs and bodies go through exactly one checker.  Returns `null` when the text is not
 * in the grammar; the caller reports a located `parse` error.
 */
class SpecParser {
  private position = 0;

  constructor(
    private readonly tokens: readonly Token[],
    private readonly spanOf: (start: number, end: number) => Span,
  ) {}

  parse(): A.Expr | null {
    const expr = this.ternary();
    if (expr === null || !this.atEnd()) return null;
    return expr;
  }

  // ---- token helpers
  private get current(): Token | undefined {
    return this.tokens[this.position];
  }

  private atEnd(): boolean {
    const token = this.current;
    return token === undefined || token.kind === "eof";
  }

  private is(text: string): boolean {
    const token = this.current;
    return token !== undefined && token.text === text && token.kind !== "eof";
  }

  private isWord(text: string): boolean {
    const token = this.current;
    return token !== undefined && token.text === text && (token.kind === "ident" || token.kind === "keyword");
  }

  private next(): Token | undefined {
    const token = this.current;
    if (token !== undefined) this.position += 1;
    return token;
  }

  private eat(text: string): boolean {
    if (!this.is(text)) return false;
    this.position += 1;
    return true;
  }

  private span(from: A.Expr, to: A.Expr): Span {
    return this.spanOf(from.span.offset, to.span.endOffset ?? to.span.offset);
  }

  private make<T extends A.Expr>(node: T): T {
    return node;
  }

  // ---- grammar
  private ternary(): A.Expr | null {
    const test = this.logicalOr();
    if (test === null) return null;
    if (!this.eat("?")) return test;
    const consequent = this.ternary();
    if (consequent === null || !this.eat(":")) return null;
    const alternate = this.ternary();
    if (alternate === null) return null;
    return { kind: "Cond", test, consequent, alternate, span: this.span(test, alternate) };
  }

  private logicalOr(): A.Expr | null {
    let left = this.logicalAnd();
    if (left === null) return null;
    while (this.is("||")) {
      this.next();
      const right = this.logicalAnd();
      if (right === null) return null;
      left = { kind: "Logical", op: "||", left, right, span: this.span(left, right) };
    }
    return left;
  }

  private logicalAnd(): A.Expr | null {
    let left = this.equality();
    if (left === null) return null;
    while (this.is("&&")) {
      this.next();
      const right = this.equality();
      if (right === null) return null;
      left = { kind: "Logical", op: "&&", left, right, span: this.span(left, right) };
    }
    return left;
  }

  private equality(): A.Expr | null {
    let left = this.relational();
    if (left === null) return null;
    for (;;) {
      const op = this.current?.text;
      if (op !== "===" && op !== "!==" && op !== "==" && op !== "!=") return left;
      this.next();
      const right = this.relational();
      if (right === null) return null;
      left = { kind: "Binary", op, left, right, span: this.span(left, right) };
    }
  }

  private relational(): A.Expr | null {
    let left = this.additive();
    if (left === null) return null;
    for (;;) {
      const op = this.current?.text;
      if (op !== "<" && op !== "<=" && op !== ">" && op !== ">=") return left;
      this.next();
      const right = this.additive();
      if (right === null) return null;
      left = { kind: "Binary", op, left, right, span: this.span(left, right) };
    }
  }

  private additive(): A.Expr | null {
    let left = this.multiplicative();
    if (left === null) return null;
    for (;;) {
      const op = this.current?.text;
      if (op !== "+" && op !== "-") return left;
      this.next();
      const right = this.multiplicative();
      if (right === null) return null;
      left = { kind: "Binary", op, left, right, span: this.span(left, right) };
    }
  }

  private multiplicative(): A.Expr | null {
    let left = this.unary();
    if (left === null) return null;
    for (;;) {
      const op = this.current?.text;
      if (op !== "*" && op !== "/" && op !== "%") return left;
      this.next();
      const right = this.unary();
      if (right === null) return null;
      left = { kind: "Binary", op, left, right, span: this.span(left, right) };
    }
  }

  private unary(): A.Expr | null {
    const token = this.current;
    if (token === undefined) return null;
    if (token.kind === "punct" && (token.text === "-" || token.text === "!" || token.text === "+" || token.text === "~")) {
      this.next();
      const operand = this.unary();
      if (operand === null) return null;
      return {
        kind: "Unary",
        op: token.text as A.UnaryOp,
        operand,
        span: this.spanOf(token.span.offset, operand.span.endOffset ?? operand.span.offset),
      };
    }
    return this.postfix();
  }

  private postfix(): A.Expr | null {
    let expr = this.primary();
    if (expr === null) return null;
    for (;;) {
      const token = this.current;
      if (token === undefined) return expr;
      if (token.text === ".") {
        this.next();
        const property = this.next();
        if (property === undefined || (property.kind !== "ident" && property.kind !== "keyword")) return null;
        expr = {
          kind: "Member",
          object: expr,
          property: property.text,
          propertySpan: this.spanOf(property.span.offset, property.span.endOffset ?? property.span.offset),
          optional: false,
          span: this.spanOf(expr.span.offset, property.span.endOffset ?? property.span.offset),
        };
        continue;
      }
      if (token.text === "[") {
        this.next();
        const index = this.ternary();
        if (index === null || !this.eat("]")) return null;
        expr = {
          kind: "Index",
          object: expr,
          index,
          optional: false,
          span: this.spanOf(expr.span.offset, index.span.endOffset ?? index.span.offset),
        };
        continue;
      }
      if (token.text === "(") {
        this.next();
        const args: A.Expr[] = [];
        if (!this.is(")")) {
          for (;;) {
            const arg = this.ternary();
            if (arg === null) return null;
            args.push(arg);
            if (!this.eat(",")) break;
          }
        }
        const close = this.current;
        if (close === undefined || !this.eat(")")) return null;
        expr = {
          kind: "Call",
          callee: expr,
          args,
          optional: false,
          span: this.spanOf(expr.span.offset, close.span.endOffset ?? close.span.offset),
        };
        continue;
      }
      return expr;
    }
  }

  private primary(): A.Expr | null {
    const token = this.next();
    if (token === undefined) return null;
    const span = this.spanOf(token.span.offset, token.span.endOffset ?? token.span.offset);
    if (token.text === "(") {
      const inner = this.ternary();
      if (inner === null) return null;
      const close = this.current;
      if (close === undefined || !this.eat(")")) return null;
      return { ...inner, span: this.spanOf(token.span.offset, close.span.endOffset ?? close.span.offset) };
    }
    if (token.kind === "number") {
      const value = numericValue(token);
      if (value === null) {
        return { kind: "Lit", lit: "float", raw: token.text, value: Number(token.text), span };
      }
      return { kind: "Lit", lit: token.numeric?.isBigInt === true ? "bigint" : "int", raw: token.text, value, span };
    }
    if (token.kind === "string") {
      return { kind: "Lit", lit: "string", raw: token.text, value: decodeString(token.text), span };
    }
    if (token.kind === "ident" || token.kind === "keyword") {
      if (token.text === "true" || token.text === "false") {
        return { kind: "Lit", lit: "boolean", raw: token.text, value: token.text === "true", span };
      }
      return { kind: "Ident", name: token.text, span };
    }
    return null;
  }
}

/** Minimal string-literal decoding for discriminant comparisons. */
function decodeString(raw: string): string {
  if (raw.length < 2) return raw;
  return raw.slice(1, -1).replace(/\\(.)/g, "$1");
}

/**
 * Parse a spec tag's expression.  Returns `null` when the tag text is empty or outside the
 * spec grammar; the caller reports the located error.
 */
export function specTagExpression(
  tag: JSDocTag,
  spanOf: (start: number, end: number) => Span,
): A.Expr | null {
  if (tag.text.trim() === "") return null;
  const lexed = lex(tag.text, tag.span.file);
  const parser = new SpecParser(lexed.tokens, spanOf);
  return parser.parse();
}

// ===========================================================================
// 4. Union aliases
// ===========================================================================

/**
 * A variant's record type: nested `Sigma` over its fields, in declaration order, with a
 * `number` field contributing its value and an `InRange` proof, terminated by `Unit`.
 */
function buildRecord(
  fields: readonly { name: string; type: TypeIR }[],
): { recordType: Term; paths: { value: number[]; inRange?: number[] }[] } {
  const components: { name: string; type: Mk; isValue: boolean }[] = [];
  const paths: { value: number[]; inRange?: number[] }[] = [];
  for (const field of fields) {
    const valueIndex = components.length;
    components.push({ name: field.name, type: typeMkOf(field.type), isValue: true });
    let inRangeIndex: number | undefined;
    if (field.type.kind === "int") {
      inRangeIndex = components.length;
      components.push({
        name: "_",
        type: (scope) => K.InRange(K.varTerm(scope.index(field.name))),
        isValue: false,
      });
    }
    const valuePath = [...Array(valueIndex).fill(1), 0];
    const inRangePath = inRangeIndex === undefined ? undefined : [...Array(inRangeIndex).fill(1), 0];
    paths.push(inRangePath === undefined ? { value: valuePath } : { value: valuePath, inRange: inRangePath });
  }
  let out: Mk = () => K.Unit;
  for (let i = components.length - 1; i >= 0; i -= 1) {
    const inner = out;
    const name = components[i]!.name;
    const type = components[i]!.type;
    out = (scope) => K.sigma(name, type(scope), inner(scope.bind(name)));
  }
  return { recordType: out(K.Scope.empty), paths };
}

/** The kernel type of a closed field type (union variants have no type parameters). */
function typeMkOf(type: TypeIR): Mk {
  switch (type.kind) {
    case "int":
      return () => K.Int;
    case "union":
      return () => type.union!.sumType;
    case "generic":
      return () => {
        throw new ExtractError("a union variant cannot have a generic field");
      };
    case "vec":
      return () => {
        throw new ExtractError("a union variant cannot have a vector field");
      };
    case "boolean":
      return () => {
        throw new ExtractError("a union variant cannot have a boolean field");
      }
  }
}

/** The `Sum` of a union's variant records, in declaration order. */
function sumTypeOf(variants: readonly VariantIR[]): Term {
  let out: Term = variants[variants.length - 1]!.recordType;
  for (let i = variants.length - 2; i >= 0; i -= 1) out = K.Sum(variants[i]!.recordType, out);
  return out;
}

/** Validate and map a `type` alias into a `UnionIR`. */
function buildUnion(alias: A.TypeAliasDecl, file: string, report: (span: Span, message: string) => void): UnionIR | null {
  if (alias.typeParams.length > 0) {
    report(alias.span, "a union type alias in the verified fragment may not have type parameters");
    return null;
  }
  if (alias.variants.length === 0) {
    report(alias.span, `the type alias \`${alias.name}\` is not a union of object variants`);
    return null;
  }
  if (alias.variants.length > 2) {
    report(
      alias.span,
      `the union \`${alias.name}\` has more than two variants; only two-variant unions are in the fragment`,
    );
    return null;
  }
  let discriminant: string | null = null;
  const tags = new Set<string>();
  const variants: VariantIR[] = [];
  for (const [index, variant] of alias.variants.entries()) {
    if (variant.fields.length === 0) {
      report(
        variant.span,
        `every variant of \`${alias.name}\` must be an object type with \`readonly\` fields`,
      );
      return null;
    }
    const disc = variant.discriminant;
    if (disc === null) {
      report(variant.span, `every variant of \`${alias.name}\` needs a string-literal discriminant field`);
      return null;
    }
    if (discriminant === null) discriminant = disc.key;
    if (disc.key !== discriminant) {
      report(disc.keySpan, `all variants of \`${alias.name}\` must share the discriminant \`${discriminant}\``);
      return null;
    }
    if (tags.has(disc.value)) {
      report(disc.valueSpan, `the discriminant value ${JSON.stringify(disc.value)} is used twice`);
      return null;
    }
    tags.add(disc.value);
    const fields: { name: string; type: TypeIR; span: Span }[] = [];
    for (const field of variant.fields) {
      if (field.name === disc.key) continue;
      if (!field.readonly) {
        report(field.span, `the field \`${field.name}\` of \`${alias.name}\` must be \`readonly\``);
        return null;
      }
      const fieldType = fieldTypeOf(field, report, alias.name);
      if (fieldType === null) return null;
      fields.push({ name: field.name, type: fieldType, span: field.span });
    }
    const { recordType, paths } = buildRecord(fields);
    variants.push({
      name: variant.name,
      tag: disc.value,
      index,
      fields: fields.map((field, i) => {
        const path = paths[i]!;
        return path.inRange === undefined
          ? { name: field.name, type: field.type, span: field.span, path: path.value }
          : { name: field.name, type: field.type, span: field.span, path: path.value, inRangePath: path.inRange };
      }),
      recordType,
      span: variant.span,
    });
  }
  return {
    name: alias.name,
    discriminant: discriminant!,
    variants,
    sumType: sumTypeOf(variants),
    file,
    span: alias.span,
  };
}

/** The type of a union-variant field: `number` only, in this milestone. */
function fieldTypeOf(
  field: A.Field,
  report: (span: Span, message: string) => void,
  aliasName: string,
): TypeIR | null {
  if (field.typeAnn.kind === "NumberType") return { kind: "int", span: field.typeAnn.span };
  if (field.typeAnn.kind === "NameType" && field.typeAnn.name === aliasName) {
    report(
      field.typeAnn.span,
      `the type alias \`${aliasName}\` is recursive; recursive types are not allowed in verified functions`,
    );
    return null;
  }
  report(
    field.typeAnn.span,
    `the field \`${field.name}\` has type \`${field.typeText}\`; only \`number\` fields are supported in a union variant`,
  );
  return null;
}

// ===========================================================================
// 5. Type resolution and file tables
// ===========================================================================

interface FileTables {
  readonly path: string;
  readonly source: string;
  readonly resolver: SpecResolver;
  readonly unions: Map<string, UnionIR>;
  readonly aliases: Map<string, A.TypeAliasDecl>;
  readonly functions: Map<string, A.FnDecl>;
  readonly importBindings: Map<string, { imported: string; specifier: string; span: Span }>;
  readonly importedAliasCache: Map<string, UnionIR>;
  readonly importedSpecs: Map<string, ImportedSpec | null>;
  readonly importedHashes: Map<string, string>;
  /** Diagnostics from building the file's own unions. */
  readonly diagnostics: Diagnostic[];
}

function scopeOf(ctx: Ctx): K.Scope {
  let scope = K.Scope.empty;
  for (const binder of ctx.binders) scope = scope.bind(binder.name);
  return scope;
}

/** Resolve a type annotation to a `TypeIR`, reporting anything outside the fragment. */
function resolveType(
  tables: FileTables,
  ctx: Ctx,
  typeParams: ReadonlySet<string>,
  ann: A.TypeAnn,
  report: (span: Span, message: string) => void,
  allowBoolean: boolean,
): TypeIR | null {
  switch (ann.kind) {
    case "NumberType":
      return { kind: "int", span: ann.span };
    case "BooleanType":
      if (allowBoolean) return { kind: "boolean", span: ann.span };
      report(ann.span, "`boolean` is only allowed as the type of a condition in verified functions");
      return null;
    case "AnyType":
      report(ann.span, "`any` is not an accepted type in verified functions");
      return null;
    case "UnknownType":
      report(ann.span, "`unknown` is not an accepted type in verified functions");
      return null;
    case "ArrayType": {
      if (!ann.readonly) {
        report(ann.span, "an array parameter must be `readonly T[]` in verified functions");
        return null;
      }
      const elem = resolveType(tables, ctx, typeParams, ann.elem, report, false);
      if (elem === null) return null;
      if (elem.kind === "vec") {
        report(ann.span, "nested arrays are not in the verified fragment");
        return null;
      }
      return { kind: "vec", elem, span: ann.span };
    }
    case "NameType": {
      if (typeParams.has(ann.name)) return { kind: "generic", typeParam: ann.name, span: ann.span };
      const union = resolveUnion(tables, ann.name, report, ann.span);
      if (union === null) return null;
      return { kind: "union", union, span: ann.span };
    }
    case "OtherType":
      report(ann.span, `the type \`${ann.text}\` is not in the verified fragment`);
      return null;
  }
}

/** A union alias declared in this file or imported from another one. */
function resolveUnion(
  tables: FileTables,
  name: string,
  report: (span: Span, message: string) => void,
  span: Span,
): UnionIR | null {
  const local = tables.unions.get(name);
  if (local !== undefined) return local;
  const binding = tables.importBindings.get(name);
  if (binding === undefined) {
    report(span, `the type \`${name}\` is not declared in this file and not imported`);
    return null;
  }
  const cached = tables.importedAliasCache.get(binding.specifier);
  if (cached !== undefined) return cached;
  const resolved = tables.resolver.resolve(tables.path, binding.specifier);
  if (!resolved.ok) {
    report(binding.span, resolved.message);
    return null;
  }
  tables.importedHashes.set(resolved.file.path, resolved.file.hash);
  const alias = specAlias(resolved.file.parsed, binding.imported);
  if (alias === undefined) {
    report(binding.span, `the imported file has no verified type alias \`${binding.imported}\``);
    return null;
  }
  const union = buildUnion(alias, resolved.file.path, report);
  if (union === null) return null;
  tables.importedAliasCache.set(binding.specifier, union);
  return union;
}

// ===========================================================================
// 6. The checker
// ===========================================================================

class Reporter {
  readonly diagnostics: Diagnostic[] = [];

  error(span: Span, message: string): void {
    this.diagnostics.push({ kind: "fragment", severity: "error", span, message });
  }

  parseError(span: Span, message: string): void {
    this.diagnostics.push({ kind: "parse", severity: "error", span, message });
  }
}

interface SignatureBuild {
  readonly signature: SignatureIR;
  readonly params: readonly ParamIR[];
  /** The signature telescope as a context, with every implicit fact already assumed. */
  readonly ctx: Ctx;
}

/** Array methods that mutate in place; every one of them is outside the fragment. */
const ARRAY_MUTATORS: ReadonlySet<string> = new Set([
  "push",
  "pop",
  "shift",
  "unshift",
  "splice",
  "sort",
  "reverse",
  "fill",
  "copyWithin",
]);

const INT_TYPE = (span: Span): TypeIR => ({ kind: "int", span });
const BOOL_TYPE = (span: Span): TypeIR => ({ kind: "boolean", span });

function refExpr(slot: Slot, type: TypeIR, span: Span): ExprIR {
  return { kind: "ref", span, type, args: [], slot, sites: [], facts: [] };
}

function goal(kind: ExprKind, args: readonly ExprIR[], type: TypeIR, span: Span): ExprIR {
  return { kind, span, type, args, sites: [], facts: [] };
}

/** Build a `Pi` telescope from a context and a body in the innermost scope. */
function telescopeType(binders: readonly Binder[], body: Term): Term {
  let out = body;
  for (let i = binders.length - 1; i >= 0; i -= 1) {
    const binder = binders[i]!;
    out = K.pi(binder.name, binder.type, out);
  }
  return out;
}

/** The `InRange` of a slot, as a proposition expression. */
function inRangeOf(slot: Slot, span: Span): ExprIR {
  return goal("inRange", [refExpr(slot, INT_TYPE(span), span)], BOOL_TYPE(span), span);
}

/**
 * Build one function's signature: the type parameters, the parameter telescope with its
 * implicit facts, the `@pre` binders and the result type with its `@post` binders.
 */
function buildSignature(
  session: Session,
  tables: FileTables,
  reporter: Reporter,
  fn: A.FnDecl,
  typeParams: ReadonlySet<string>,
  ids: Ids,
): SignatureBuild | null {
  let ctx: Ctx = { binders: [], facts: [], narrowings: [], ids };
  const typeParamBinders: Binder[] = [];
  for (const param of fn.typeParams) {
    if (typeParams.has(param.name) && typeParamBinders.some((b) => b.surface === param.name)) {
      reporter.error(param.span, `the type parameter \`${param.name}\` is declared twice`);
      continue;
    }
    const bound = bind(ctx, param.name, K.sort(0), "type-param", param.name, param.span);
    ctx = bound.ctx;
    typeParamBinders.push(bound.binder);
  }

  const params: ParamIR[] = [];
  for (const param of fn.params) {
    if (param.rest) {
      reporter.error(param.span, "rest parameters are not in the verified fragment");
      continue;
    }
    if (param.optional) {
      reporter.error(param.span, "optional parameters are not in the verified fragment");
      continue;
    }
    if (param.defaultText !== undefined) {
      reporter.error(param.span, "default parameter values are not in the verified fragment");
      continue;
    }
    if (param.typeAnn === undefined) {
      reporter.error(param.nameSpan, `the parameter \`${param.name}\` needs an explicit type annotation`);
      continue;
    }
    const type = resolveType(tables, ctx, typeParams, param.typeAnn, (span, message) => reporter.error(span, message), false);
    if (type === null) continue;
    const built = bindParam(ctx, param.name, type, param.span);
    ctx = built.ctx;
    params.push({ name: param.name, binder: built.binder, type, extra: built.extra, span: param.span });
  }

  // ---- @pre -----------------------------------------------------------------
  const preconditions: FactIR[] = [];
  const preTags = fn.jsdoc === null ? [] : tagsNamed(fn.jsdoc, "pre");
  const specCtx = ctx;
  const checker = new FnChecker(session, tables, reporter, fn, typeParams, specCtx, null);
  const preEnv = envOfParams(params);
  preTags.forEach((tag, index) => {
    const ast = checker.parseTag(tag);
    if (ast === null) return;
    const expr = checker.checkExpression(ast, ctx, preEnv, {});
    if (expr === null) return;
    if (expr.type.kind !== "boolean") {
      reporter.error(tag.textSpan, "`@pre` must be a boolean expression");
      return;
    }
    const bound = bind(ctx, `pre${index}`, exprTerm(ctx, expr), "pre", undefined, tag.span);
    ctx = bound.ctx;
    preconditions.push({ prop: expr, origin: "pre", binder: bound.binder, text: renderExpr(expr) });
  });

  // ---- result ---------------------------------------------------------------
  if (fn.returnType === undefined) {
    reporter.error(fn.nameSpan, `the function \`${fn.name}\` needs an explicit return type annotation`);
    return null;
  }
  const resultType = resolveType(
    tables,
    ctx,
    typeParams,
    fn.returnType,
    (span, message) => reporter.error(span, message),
    false,
  );
  if (resultType === null) return null;

  const postTags = fn.jsdoc === null ? [] : tagsNamed(fn.jsdoc, "post");
  const result = buildResult(reporter, fn, ctx, resultType, postTags, checker, envOfParams(params));
  if (result === null) return null;

  const signature: SignatureIR = {
    binders: ctx.binders,
    preconditions,
    result,
    type: telescopeType(ctx.binders, result.term),
  };
  return { signature, params, ctx };
}

/** Bind a parameter and its implicit companions (length, element guard, `InRange`). */
function bindParam(
  ctx: Ctx,
  name: string,
  type: TypeIR,
  span: Span,
): { ctx: Ctx; binder: Binder; extra: Binder[] } {
  const extra: Binder[] = [];
  if (type.kind === "int") {
    const value = bind(ctx, name, K.Int, "param", name, span);
    const proof = bind(value.ctx, `r_${name}`, K.InRange(K.varTerm(0)), "in-range", undefined, span);
    const fact: FactIR = {
      prop: inRangeOf({ kind: "binder", binder: value.binder }, span),
      origin: "param-in-range",
      binder: proof.binder,
      text: `InRange ${name}`,
    };
    extra.push(proof.binder);
    return { ctx: withFact(proof.ctx, fact), binder: value.binder, extra };
  }
  if (type.kind === "vec") {
    const len = bind(ctx, `n_${name}`, K.Int, "vec-len", undefined, span);
    const lenSlot: Slot = { kind: "binder", binder: len.binder };
    const lenRef = refExpr(lenSlot, INT_TYPE(span), span);
    const vecType = K.Vec(elemKernelType(len.ctx, type.elem!), K.varTerm(0));
    const value = bind(len.ctx, name, vecType, "param", name, span);
    const bounds: FactIR = {
      prop: goal(
        "and",
        [
          goal("le", [goal("int", [], INT_TYPE(span), span), lenRef], BOOL_TYPE(span), span),
          goal("le", [lenRef, goal("int", [], INT_TYPE(span), span)], BOOL_TYPE(span), span),
        ],
        BOOL_TYPE(span),
        span,
      ),
      origin: "vec-bounds",
      text: `0 <= ${name}.length <= 4294967295`,
    };
    let out = withFact(value.ctx, bounds);
    extra.push(len.binder);
    if (type.elem!.kind === "int") {
      // `elems_a : (i : Int) -> (p : And (Le 0 i) (Lt i n_a)) -> InRange (get Int n_a a i p)`:
      // the fact a `readonly number[]` read needs, and the one the runtime boundary guard
      // supplies (section 6.3).
      const scope = scopeOf(out);
      const elemsType = ((s: K.Scope) =>
        K.pi(
          "i",
          K.Int,
          K.pi(
            "p",
            K.And(K.Le(K.intLit(0n), K.varTerm(s.bind("i").index("i"))), K.Lt(K.varTerm(s.bind("i").index("i")), K.varTerm(s.bind("i").index(`n_${name}`)))),
            K.InRange(
              K.Get(
                K.Int,
                K.varTerm(s.bind("i").bind("p").index(`n_${name}`)),
                K.varTerm(s.bind("i").bind("p").index(name)),
                K.varTerm(s.bind("i").bind("p").index("i")),
                K.varTerm(s.bind("i").bind("p").index("p")),
              ),
            ),
          ),
        ))(scope);
      const elems = bind(out, `elems_${name}`, elemsType, "vec-elems", undefined, span);
      out = elems.ctx;
      extra.push(elems.binder);
    }
    return { ctx: out, binder: value.binder, extra };
  }
  const bound = bind(ctx, name, valueKernelType(ctx, type), "param", name, span);
  return { ctx: bound.ctx, binder: bound.binder, extra };
}

/** The `@post` binders and the codomain type. */
function buildResult(
  reporter: Reporter,
  fn: A.FnDecl,
  ctx: Ctx,
  surfaceType: TypeIR,
  postTags: readonly JSDocTag[],
  checker: FnChecker,
  baseEnv: FnEnv,
): ResultIR | null {
  const shape: ResultShape =
    surfaceType.kind === "int"
      ? "int"
      : surfaceType.kind === "vec"
        ? "vec"
        : surfaceType.kind === "union"
          ? "union"
          : "generic";
  if (postTags.length > 0 && (shape === "generic" || shape === "union")) {
    reporter.error(
      postTags[0]!.span,
      `\`@post\` is not supported for a \`${shape === "generic" ? "generic" : "union"}\` result`,
    );
    return null;
  }
  const returnSpan = fn.returnType?.span ?? fn.nameSpan;
  if (shape === "generic" || shape === "union") {
    return {
      shape,
      type: surfaceType,
      term: valueKernelType(ctx, surfaceType),
      posts: [],
      layout: { shape, valuePath: [] },
    };
  }

  const resultName = shape === "int" ? "r" : "m";
  const bound = bind(ctx, resultName, K.Int, "result", "result", returnSpan);
  const resultCtx = bound.ctx;
  const resultRef: ExprIR =
    shape === "vec"
      ? {
          ...refExpr({ kind: "result" }, surfaceType, returnSpan),
          vecLength: refExpr({ kind: "binder", binder: bound.binder }, INT_TYPE(returnSpan), returnSpan),
        }
      : refExpr({ kind: "result" }, surfaceType, returnSpan);
  const env = envWithResult(resultRef, baseEnv);

  const posts: FactIR[] = [];
  for (const tag of postTags) {
    const ast = checker.parseTag(tag);
    if (ast === null) continue;
    const expr = checker.checkExpression(ast, resultCtx, env, {});
    if (expr === null) continue;
    if (expr.type.kind !== "boolean") {
      reporter.error(tag.textSpan, "`@post` must be a boolean expression");
      continue;
    }
    posts.push({ prop: expr, origin: "condition", text: renderExpr(expr) });
  }

  const postTerms = posts.map((post) => exprTerm(resultCtx, post.prop, { result: K.varTerm(0) }));
  let codomain: Term;
  if (shape === "int") {
    codomain = K.sigma(resultName, K.Int, andAll([K.InRange(K.varTerm(0)), ...postTerms]));
  } else {
    const vec = K.Vec(elemKernelType(resultCtx, surfaceType.elem!), K.varTerm(0));
    codomain = K.sigma(resultName, K.Int, postTerms.length === 0 ? vec : K.And(vec, andAll(postTerms)));
  }
  const layout: ResultLayout =
    shape === "int"
      ? posts.length === 0
        ? { shape, valuePath: [0], inRangePath: [1] }
        : { shape, valuePath: [0], inRangePath: [1, 0], postPath: [1, 1] }
      : posts.length === 0
        ? { shape, valuePath: [1, 0], lengthPath: [0], vecPath: [1, 0] }
        : { shape, valuePath: [1, 0], lengthPath: [0], vecPath: [1, 0], postPath: [1, 1] };

  return {
    shape,
    type: surfaceType,
    binder: bound.binder,
    term: codomain,
    posts,
    layout,
  };
}

/** The environment a `@post` is checked in: the parameters plus `result`. */
function envWithResult(resultRef: ExprIR, base: FnEnv): FnEnv {
  const variable: EnvVar = {
    name: "result",
    slot: { kind: "result" },
    type: resultRef.type,
    mutable: false,
    param: true,
    span: resultRef.span,
    lengthExpr: resultRef.vecLength,
  };
  const vars = new Map(base.vars);
  vars.set("result", variable);
  return { vars };
}

/** The starting environment of a function body: its parameters. */
function envOfParams(params: readonly ParamIR[]): FnEnv {
  const vars = new Map<string, EnvVar>();
  for (const param of params) {
    const lengthBinder = param.type.kind === "vec" ? param.extra[0] : undefined;
    vars.set(param.name, {
      name: param.name,
      slot: { kind: "binder", binder: param.binder },
      type: param.type,
      mutable: false,
      param: true,
      span: param.span,
      lengthExpr:
        lengthBinder === undefined ? undefined : refExpr({ kind: "binder", binder: lengthBinder }, INT_TYPE(param.span), param.span),
    });
  }
  return { vars };
}

// ---------------------------------------------------------------------------
// The per-function checker
// ---------------------------------------------------------------------------

interface ExpressionOptions {
  /** String literals are allowed (they are only compared with discriminants). */
  readonly allowString?: boolean;
  /** Discriminant field accesses are allowed. */
  readonly allowDiscriminant?: boolean;
  /** The expected type, when the caller knows it (object literals need it). */
  readonly expected?: TypeIR | null;
}

export interface CondResult {
  readonly cond: CondIR;
  readonly thenCtx: Ctx;
  readonly elseCtx: Ctx;
}

class FnChecker implements LoopHost {
  readonly ids: Ids;
  readonly sites: ObligationSite[] = [];
  readonly imports: ImportedSpec[] = [];
  readonly loops: LoopIR[] = [];
  recursive = false;
  /** While checking a spec (an invariant or a measure) no body obligation is recorded. */
  specDepth = 0;

  constructor(
    private readonly session: Session,
    private readonly tables: FileTables,
    private readonly reporter: Reporter,
    private readonly fn: A.FnDecl,
    private readonly typeParams: ReadonlySet<string>,
    private readonly signatureCtx: Ctx,
    private readonly resultType: Term | null,
  ) {
    this.ids = session.ids;
  }

  // ---- LoopHost -------------------------------------------------------------

  bindBinder(
    ctx: Ctx,
    name: string,
    type: Term,
    role: BinderRole,
    surface?: string,
    span?: Span,
  ): { ctx: Ctx; binder: Binder } {
    return bind(ctx, name, type, role, surface, span);
  }

  addFact(ctx: Ctx, prop: ExprIR, origin: FactOrigin, binder?: Binder): Ctx {
    return withFact(ctx, { prop, origin, binder, text: renderExpr(prop) });
  }

  parseTag(tag: JSDocTag): A.Expr | null {
    const table = this.tables;
    const spanOf = (start: number, end: number): Span =>
      spanFromOffsets(
        table.path,
        table.source,
        tagSourceOffset(tag, start),
        tagSourceOffset(tag, Math.max(start, end)),
      );
    const ast = specTagExpression(tag, spanOf);
    if (ast === null) this.reporter.parseError(tag.textSpan, "cannot parse this spec expression");
    return ast;
  }

  condition(ast: A.Expr, ctx: Ctx, env: FnEnv, spec = false): CondIR | null {
    if (!spec) {
      const result = this.conditionWithScopes(ast, ctx, env);
      return result === null ? null : result.cond;
    }
    this.specDepth += 1;
    try {
      const result = this.conditionWithScopes(ast, ctx, env);
      return result === null ? null : result.cond;
    } finally {
      this.specDepth -= 1;
    }
  }

  /** The condition plus the two extended branch scopes (used by the statement walker). */
  conditionWithScopes(ast: A.Expr, ctx: Ctx, env: FnEnv): CondResult | null {
    const expr = this.checkExpression(ast, ctx, env, { allowDiscriminant: true });
    if (expr === null) return null;
    if (expr.kind === "tagTest") {
      const test: TagTestIR = {
        subject: expr.slot!,
        union: expr.union!,
        variant: expr.variant!,
        positive: expr.literal === true,
      };
      if (expr.union!.variants.length !== 2) {
        this.reporter.error(ast.span, "a discriminant test is only supported for two-variant unions");
        return null;
      }
      const variant = test.variant;
      const other = expr.union!.variants.find((v) => v.index !== variant.index)!;
      const thenVariant = test.positive ? variant : other;
      const elseVariant = test.positive ? other : variant;
      const positive = test.positive;
      const thenBind = bind(
        ctx,
        `v_${thenVariant.tag}`,
        thenVariant.recordType,
        "payload",
        `v_${thenVariant.tag}`,
        ast.span,
      );
      const elseBind = bind(
        ctx,
        `v_${elseVariant.tag}`,
        elseVariant.recordType,
        "payload",
        `v_${elseVariant.tag}`,
        ast.span,
      );
      const thenNarrowing: Narrowing = {
        subject: test.subject,
        union: expr.union!,
        variant: thenVariant,
        allowed: [thenVariant.tag],
        payload: thenBind.binder,
      };
      const elseNarrowing: Narrowing = {
        subject: test.subject,
        union: expr.union!,
        variant: elseVariant,
        allowed: [elseVariant.tag],
        payload: elseBind.binder,
      };
      const truth = goal("true", [], BOOL_TYPE(ast.span), ast.span);
      const cond: CondIR = {
        expr,
        thenBinder: thenBind.binder,
        elseBinder: elseBind.binder,
        prop: truth,
        thenNarrowings: [thenNarrowing],
        elseNarrowings: [elseNarrowing],
        tagTest: test,
      };
      void positive;
      return {
        cond,
        thenCtx: withNarrowings(withFact(thenBind.ctx, tagFact(test, truth)), [thenNarrowing]),
        elseCtx: withNarrowings(
          withFact(elseBind.ctx, tagFact({ ...test, positive: !test.positive }, truth)),
          [elseNarrowing],
        ),
      };
    }
    if (!isComparison(expr) && expr.kind !== "true") {
      this.reporter.error(ast.span, "a condition must be an integer comparison or a discriminant test");
      return null;
    }
    if (expr.kind === "true") {
      const truth = this.trueExpr(ast.span);
      const thenBind = bind(ctx, "h", K.Unit, "hypothesis", undefined, ast.span);
      const elseBind = bind(thenBind.ctx, "h", K.Unit, "hypothesis", undefined, ast.span);
      return {
        cond: {
          expr: truth,
          thenBinder: thenBind.binder,
          elseBinder: elseBind.binder,
          prop: truth,
          thenNarrowings: [],
          elseNarrowings: [],
        },
        thenCtx: thenBind.ctx,
        elseCtx: elseBind.ctx,
      };
    }
    // An integer comparison: the then branch assumes it, the else branch assumes its
    // integer complement (`Lt`/`Le` swap, which is what `ifLe` hands each side).
    const thenType = safePropTerm(ctx, expr);
    const complement = negateCondition(expr);
    const elseType = safePropTerm(ctx, complement);
    const thenBind = bind(ctx, "h", thenType, "hypothesis", undefined, ast.span);
    const elseBind = bind(thenBind.ctx, "h", elseType, "hypothesis", undefined, ast.span);
    const cond: CondIR = {
      expr,
      thenBinder: thenBind.binder,
      elseBinder: elseBind.binder,
      prop: expr,
      thenNarrowings: [],
      elseNarrowings: [],
    };
    return {
      cond,
      thenCtx: withFact(thenBind.ctx, {
        prop: expr,
        origin: "condition",
        binder: thenBind.binder,
        text: renderExpr(expr),
      }),
      elseCtx: withFact(thenBind.ctx, {
        prop: complement,
        origin: "condition",
        binder: elseBind.binder,
        text: renderExpr(complement),
      }),
    };
  }

  expression(ast: A.Expr, ctx: Ctx, env: FnEnv, spec = false): ExprIR | null {
    if (!spec) return this.checkExpression(ast, ctx, env, {});
    this.specDepth += 1;
    try {
      return this.checkExpression(ast, ctx, env, {});
    } finally {
      this.specDepth -= 1;
    }
  }

  conjoin(parts: readonly ExprIR[], ctx: Ctx, env: FnEnv, span: Span): ExprIR {
    void env;
    if (parts.length === 0) return this.trueExpr(span);
    let out = parts[parts.length - 1]!;
    for (let i = parts.length - 2; i >= 0; i -= 1) {
      const type = safePropTerm(ctx, parts[i]!);
      const bound = bind(ctx, `h${i}`, type, "hypothesis", undefined, span);
      out = {
        kind: "and",
        span,
        type: BOOL_TYPE(span),
        args: [parts[i]!, out],
        rightBinder: bound.binder,
        sites: [],
        facts: [],
      };
    }
    return out;
  }

  site(kind: ObligationKind, span: Span, ctx: Ctx, goalExpr: ExprIR, resultValue?: ExprIR): ObligationSite {
    const site: ObligationSite = {
      id: this.ids.fresh(),
      kind,
      span,
      context: ctx.binders,
      hypotheses: ctx.facts,
      goal: goalExpr,
      resultValue,
      text: renderExpr(goalExpr),
    };
    if (this.specDepth === 0) this.sites.push(site);
    return site;
  }

  ref(slot: Slot, type: TypeIR, span: Span): ExprIR {
    return refExpr(slot, type, span);
  }

  scope(ctx: Ctx): K.Scope {
    return scopeOf(ctx);
  }

  typeMk(type: TypeIR): Mk {
    switch (type.kind) {
      case "int":
        return () => K.Int;
      case "union":
        return () => type.union!.sumType;
      case "generic":
        return (scope) => K.varTerm(scope.index(type.typeParam!));
      case "vec":
        return () => {
          throw new ExtractError("a vector type needs its length");
        };
      case "boolean":
        return () => {
          throw new ExtractError("`boolean` is only allowed as a condition");
        };
    }
  }

  term(ctx: Ctx, expr: ExprIR): Term {
    return exprTerm(ctx, expr);
  }

  le(a: ExprIR, b: ExprIR, span: Span): ExprIR {
    return goal("le", [a, b], BOOL_TYPE(span), span);
  }

  lt(a: ExprIR, b: ExprIR, span: Span): ExprIR {
    return goal("lt", [a, b], BOOL_TYPE(span), span);
  }

  inRange(a: ExprIR, span: Span): ExprIR {
    return goal("inRange", [a], BOOL_TYPE(span), span);
  }

  trueExpr(span: Span): ExprIR {
    return goal("true", [], BOOL_TYPE(span), span);
  }

  intExpr(value: bigint, span: Span): ExprIR {
    return { kind: "int", span, type: INT_TYPE(span), args: [], literal: value, sites: [], facts: [] };
  }

  report(span: Span, message: string): void {
    this.reporter.error(span, message);
  }

  walk(stmts: readonly A.Stmt[], ctx: Ctx, env: FnEnv, k: Continuation, loop: LoopIR | null): StmtIR[] {
    const out: StmtIR[] = [];
    for (let i = 0; i < stmts.length; i += 1) {
      const stmt = stmts[i]!;
      switch (stmt.kind) {
        case "Empty":
          continue;
        case "Block": {
          const spliced = [...stmt.body, ...stmts.slice(i + 1)];
          return [...out, ...this.walk(spliced, ctx, env, k, loop)];
        }
        case "VarDecl": {
          for (const declaration of stmt.declarations) {
            if (stmt.declKind === "var") {
              this.reporter.error(
                stmt.span,
                "`var` declarations are not allowed in verified functions; use `const` or `let`",
              );
              continue;
            }
            if (declaration.init === undefined) {
              this.reporter.error(declaration.span, `\`${declaration.name}\` needs an initializer`);
              continue;
            }
            const checked = this.checkExpression(declaration.init, ctx, env, {});
            if (checked === null) continue;
            const mutable = stmt.declKind === "let";
            const bound = bind(ctx, declaration.name, valueKernelType(ctx, checked.type), "local", declaration.name, declaration.nameSpan);
            ctx = bound.ctx;
            env = envWith(env, {
              name: declaration.name,
              slot: { kind: "binder", binder: bound.binder },
              type: checked.type,
              mutable,
              param: false,
              span: declaration.nameSpan,
              lengthExpr: checked.vecLength,
            });
            out.push({ kind: "local", binder: bound.binder, value: checked, mutable, span: declaration.span });
          }
          continue;
        }
        case "ExprStmt": {
          const assigned = this.assignment(stmt.expr, ctx, env, loop);
          if (assigned !== null) {
            ctx = assigned.ctx;
            env = assigned.env;
            out.push(...assigned.stmts);
            continue;
          }
          const checked = this.checkExpression(stmt.expr, ctx, env, {});
          if (checked !== null) out.push({ kind: "expr", expr: checked, span: stmt.span });
          continue;
        }
        case "Return": {
          const site = this.returnSite(stmt, ctx, env);
          if (site === null) return [...out, { kind: "nop", span: stmt.span }];
          out.push({ kind: "return", value: site.value, site: site.site, span: stmt.span });
          return out;
        }
        case "If": {
          const normalized = normalizeIf(stmt);
          const condition = this.conditionWithScopes(normalized.test, ctx, env);
          if (condition === null) {
            out.push({ kind: "nop", span: stmt.span });
            return out;
          }
          const after: Continuation = (nextCtx, nextEnv) =>
            this.walk(stmts.slice(i + 1), nextCtx, nextEnv, k, loop);
          const thenIr = this.walk(
            normalized.then.kind === "Block" ? normalized.then.body : [normalized.then],
            condition.thenCtx,
            env,
            after,
            loop,
          );
          const elseIr =
            normalized.alternate === null
              ? after(condition.elseCtx, env)
              : this.walk(
                  normalized.alternate.kind === "Block" ? normalized.alternate.body : [normalized.alternate],
                  condition.elseCtx,
                  env,
                  after,
                  loop,
                );
          out.push({ kind: "if", cond: condition.cond, then: thenIr, otherwise: elseIr, span: stmt.span });
          return out;
        }
        case "Switch": {
          const after: Continuation = (nextCtx, nextEnv) =>
            this.walk(stmts.slice(i + 1), nextCtx, nextEnv, k, loop);
          const switched = this.switch(stmt, ctx, env, after, loop);
          out.push(switched);
          return out;
        }
        case "While":
        case "For": {
          const lowered = lowerLoop(this, {
            ast: stmt,
            ctx,
            env,
            rest: stmts.slice(i + 1),
            k,
            resultType: this.resultType ?? K.Int,
            span: stmt.span,
          });
          if (lowered === null) {
            out.push({ kind: "nop", span: stmt.span });
            return out;
          }
          this.loops.push(lowered);
          out.push({ kind: "loop", loop: lowered, span: stmt.span });
          return out;
        }
        case "Throw":
          this.reporter.error(stmt.span, "`throw` is not allowed in verified functions");
          out.push({ kind: "nop", span: stmt.span });
          return out;
        case "Break":
          this.reporter.error(stmt.span, "`break` is not allowed in verified functions");
          out.push({ kind: "nop", span: stmt.span });
          return out;
        case "Continue":
          this.reporter.error(stmt.span, "`continue` is not allowed in verified functions");
          out.push({ kind: "nop", span: stmt.span });
          return out;
        case "Unsupported":
          this.reporter.error(
            stmt.span,
            `\`${stmt.what.replace(/`/g, "")}\` is not allowed in verified functions`,
          );
          out.push({ kind: "nop", span: stmt.span });
          return out;
      }
    }
    return [...out, ...k(ctx, env)];
  }

  // ---- assignment -----------------------------------------------------------

  private assignment(
    ast: A.Expr,
    ctx: Ctx,
    env: FnEnv,
    loop: LoopIR | null,
  ): { ctx: Ctx; env: FnEnv; stmts: StmtIR[] } | null {
    let target: A.Expr;
    let value: A.Expr;
    if (ast.kind === "Assign") {
      target = ast.target;
      if (ast.op !== "=" && ast.op !== "+=" && ast.op !== "-=") {
        this.reporter.error(ast.span, `the assignment operator \`${ast.op}\` is not allowed in verified functions`);
        return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
      }
      value =
        ast.op === "="
          ? ast.value
          : {
              kind: "Binary",
              op: ast.op === "+=" ? "+" : "-",
              left: target,
              right: ast.value,
              span: ast.span,
            };
    } else if (ast.kind === "Update") {
      target = ast.operand;
      const one: A.Lit = { kind: "Lit", lit: "int", raw: "1", value: 1n, span: ast.span };
      value = { kind: "Binary", op: ast.op === "++" ? "+" : "-", left: ast.operand, right: one, span: ast.span };
    } else {
      return null;
    }
    if (target.kind === "Index") {
      this.reporter.error(target.span, "array mutation is not allowed in verified functions");
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    if (target.kind !== "Ident") {
      this.reporter.error(target.span, "only a plain variable may be assigned in verified functions");
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    const variable = envLookup(env, target.name);
    if (variable === undefined) {
      this.reporter.error(target.span, `unresolved name \`${target.name}\``);
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    if (variable.param) {
      this.reporter.error(target.span, `mutating the parameter \`${target.name}\` is not allowed in verified functions`);
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    if (!variable.mutable) {
      this.reporter.error(
        target.span,
        `\`${target.name}\` is a \`const\`; only \`let\` variables may be assigned in verified functions`,
      );
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    if (loop === null) {
      this.reporter.error(
        target.span,
        `\`${target.name}\` may only be reassigned inside a loop of the same function`,
      );
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    const checked = this.checkExpression(value, ctx, env, { expected: variable.type });
    if (checked === null) return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    if (!typesMatch(variable.type, checked.type)) {
      this.reporter.error(ast.span, `cannot assign \`${renderExpr(checked)}\` to \`${target.name}\``);
      return { ctx, env, stmts: [{ kind: "nop", span: ast.span }] };
    }
    const bound = bind(ctx, `${target.name}'`, valueKernelType(ctx, variable.type), "local", target.name, target.span);
    const nextEnv = envWith(env, { ...variable, slot: { kind: "binder", binder: bound.binder } });
    return {
      ctx: bound.ctx,
      env: nextEnv,
      stmts: [{ kind: "local", binder: bound.binder, value: checked, mutable: true, span: ast.span }],
    };
  }

  // ---- returns --------------------------------------------------------------

  private returnSite(
    stmt: A.ReturnStmt,
    ctx: Ctx,
    env: FnEnv,
  ): { value: ExprIR; site: ObligationSite } | null {
    if (stmt.argument === null) {
      this.reporter.error(stmt.span, "a verified function must return a value");
      return null;
    }
    const checked = this.checkExpression(stmt.argument, ctx, env, { expected: this.resultSurfaceType() });
    if (checked === null) return null;
    const result = this.result();
    if (result === null) return null;
    const resultExpr: ExprIR =
      result.shape === "vec" && checked.vecLength !== undefined
        ? { ...refExpr({ kind: "result" }, result.type, stmt.span), vecLength: checked.vecLength }
        : refExpr({ kind: "result" }, result.type, stmt.span);
    const parts: ExprIR[] = [];
    if (result.shape === "int") parts.push(inRangeOf({ kind: "result" }, stmt.span));
    // `result.length` is the result *binder* (`m : Int`) in the codomain, but a body
    // obligation lives outside that binder: substitute the returned vector's length (or the
    // returned value, for the `int` shape) for it, exactly like `result` itself.
    const resultBinderId = result.binder?.id;
    for (const post of result.posts) {
      parts.push(substituteExpr(post.prop, (e) => {
        if (e.kind === "ref" && e.slot?.kind === "result") return resultExpr;
        if (
          resultBinderId !== undefined &&
          e.kind === "ref" &&
          e.slot?.kind === "binder" &&
          e.slot.binder.id === resultBinderId
        ) {
          return result.shape === "vec" ? checked.vecLength ?? null : checked;
        }
        return null;
      }));
    }
    const goalExpr = parts.length === 0 ? this.trueExpr(stmt.span) : this.conjoin(parts, ctx, env, stmt.span);
    const site = this.site("post", stmt.span, ctx, goalExpr, checked);
    return { value: checked, site };
  }

  private result(): ResultIR | null {
    return this.resultSummary;
  }

  resultSummary: ResultIR | null = null;

  private resultSurfaceType(): TypeIR | null {
    return this.resultSummary?.type ?? null;
  }

  // ---- switch ---------------------------------------------------------------

  private switch(
    stmt: A.SwitchStmt,
    ctx: Ctx,
    env: FnEnv,
    k: Continuation,
    loop: LoopIR | null,
  ): StmtIR {
    const subjectExpr = this.checkExpression(stmt.discriminant, ctx, env, { allowDiscriminant: true });
    const subjectUnion = subjectExpr?.union ?? subjectExpr?.type.union;
    if (subjectExpr === null || subjectExpr.slot === undefined || subjectUnion === undefined) {
      this.reporter.error(stmt.discriminant.span, "a `switch` must discriminate on a union discriminant");
      return { kind: "nop", span: stmt.span };
    }
    const union = subjectUnion;
    const subject = subjectExpr.slot;
    const seen = new Set<string>();
    const cases: SwitchCaseIR[] = [];
    for (const switchCase of stmt.cases) {
      if (switchCase.test === null) {
        this.reporter.error(switchCase.span, "a `default` case is not allowed: the switch must be exhaustive");
        continue;
      }
      if (switchCase.test.kind !== "Lit" || switchCase.test.lit !== "string") {
        this.reporter.error(switchCase.test.span, "every case of a `switch` must be a discriminant string literal");
        continue;
      }
      const tag = String(switchCase.test.value);
      const variant = union.variants.find((v) => v.tag === tag);
      if (variant === undefined) {
        this.reporter.error(switchCase.test.span, `\`${tag}\` is not a variant of \`${union.name}\``);
        continue;
      }
      if (seen.has(tag)) {
        this.reporter.error(switchCase.test.span, `the case \`${tag}\` appears twice`);
        continue;
      }
      seen.add(tag);
      const payload = bind(ctx, `v_${tag}`, variant.recordType, "payload", `v_${tag}`, switchCase.span);
      const narrowing: Narrowing = {
        subject,
        union,
        variant,
        allowed: [tag],
        payload: payload.binder,
      };
      const caseCtx = withNarrowings(
        withFact(payload.ctx, {
          prop: goal("true", [], BOOL_TYPE(switchCase.span), switchCase.span),
          origin: "tag-test",
          binder: payload.binder,
          text: `${slotText(subject)}.${union.discriminant} === ${JSON.stringify(tag)}`,
        }),
        [narrowing],
      );
      const body = this.walk(switchCase.body, caseCtx, env, k, loop);
      const last = switchCase.body[switchCase.body.length - 1];
      if (last === undefined || last.kind !== "Return") {
        this.reporter.error(switchCase.span, "every case of a `switch` in a verified function must end with `return`");
      }
      cases.push({ tag, variant, payload: payload.binder, body, span: switchCase.span });
    }
    for (const variant of union.variants) {
      if (!seen.has(variant.tag)) {
        this.reporter.error(stmt.span, `the switch must cover the variant ${JSON.stringify(variant.tag)}`);
      }
    }
    return { kind: "switch", subject, union, cases, span: stmt.span };
  }

  // ---- expressions ----------------------------------------------------------

  checkExpression(ast: A.Expr, ctx: Ctx, env: FnEnv, options: ExpressionOptions): ExprIR | null {
    switch (ast.kind) {
      case "Lit": {
        if (ast.lit === "int" || ast.lit === "hex") {
          return this.intExpr(typeof ast.value === "bigint" ? ast.value : BigInt(ast.value), ast.span);
        }
        if (ast.lit === "float") {
          this.reporter.error(ast.span, "float literals are not allowed in verified functions");
          return null;
        }
        if (ast.lit === "bigint") {
          this.reporter.error(ast.span, "`bigint` literals are not in the verified fragment");
          return null;
        }
        if (ast.lit === "boolean") {
          this.reporter.error(ast.span, "boolean literals are not in the verified fragment");
          return null;
        }
        if (ast.lit === "string") {
          if (!options.allowString) {
            this.reporter.error(ast.span, "string literals are only allowed as union discriminants");
            return null;
          }
          return { kind: "string", span: ast.span, type: BOOL_TYPE(ast.span), args: [], literal: String(ast.value), sites: [], facts: [] };
        }
        this.reporter.error(ast.span, "regex literals are not in the verified fragment");
        return null;
      }
      case "Ident": {
        const variable = envLookup(env, ast.name);
        if (variable === undefined) {
          this.reporter.error(ast.span, `unresolved name \`${ast.name}\``);
          return null;
        }
        const base = refExpr(variable.slot, variable.type, ast.span);
        if (variable.type.kind === "vec" && variable.lengthExpr !== undefined) {
          return { ...base, vecLength: variable.lengthExpr };
        }
        return base;
      }
      case "This":
        this.reporter.error(ast.span, "`this` is not allowed in verified functions");
        return null;
      case "Member":
        return this.member(ast, ctx, env, options);
      case "Index":
        return this.index(ast, ctx, env);
      case "Call":
        return this.call(ast, ctx, env);
      case "Unary":
        return this.unary(ast, ctx, env);
      case "Update":
        this.reporter.error(
          ast.span,
          `\`${ast.op}\` is only allowed as a loop update statement in verified functions`,
        );
        return null;
      case "Binary":
        return this.binary(ast, ctx, env);
      case "Logical":
        return this.logical(ast, ctx, env);
      case "Cond":
        return this.conditional(ast, ctx, env);
      case "Assign":
        this.reporter.error(ast.span, "assignments are statements only in verified functions");
        return null;
      case "Arrow":
        this.reporter.error(ast.span, "arrow functions and closures are not allowed in verified functions");
        return null;
      case "As":
        this.reporter.error(ast.span, "`as` casts are not allowed in verified functions");
        return null;
      case "NonNull":
        this.reporter.error(ast.span, "non-null assertions (`!`) are not allowed in verified functions");
        return null;
      case "Spread":
        this.reporter.error(ast.span, "spread (`...`) is only allowed inside an array literal");
        return null;
      case "Await":
        this.reporter.error(ast.span, "`await` is not allowed in verified functions");
        return null;
      case "Yield":
        this.reporter.error(ast.span, "`yield` is not allowed in verified functions");
        return null;
      case "Seq":
        this.reporter.error(ast.span, "the comma operator is not allowed in verified functions");
        return null;
      case "Template":
        this.reporter.error(ast.span, "template literals are not allowed in verified functions");
        return null;
      case "New":
        this.reporter.error(ast.span, "`new` is not allowed in verified functions");
        return null;
      case "ArrayLit":
        return this.arrayLiteral(ast, ctx, env);
      case "ObjectLit":
        return this.objectLiteral(ast, ctx, env, options);
      case "Unsupported":
        this.reporter.error(ast.span, `\`${ast.what.replace(/`/g, "")}\` is not allowed in verified functions`);
        return null;
    }
  }

  private member(ast: A.MemberExpr, ctx: Ctx, env: FnEnv, options: ExpressionOptions): ExprIR | null {
    if (ast.optional) {
      this.reporter.error(ast.span, "optional chaining (`?.`) is not allowed in verified functions");
      return null;
    }
    const object = this.checkExpression(ast.object, ctx, env, { allowDiscriminant: options.allowDiscriminant });
    if (object === null) return null;
    if (ast.property === "length") {
      if (object.type.kind !== "vec" || object.vecLength === undefined) {
        this.reporter.error(ast.span, "`.length` is only available on a `readonly T[]` value");
        return null;
      }
      return { kind: "length", span: ast.span, type: INT_TYPE(ast.span), args: [object], vecLength: object.vecLength, sites: [], facts: [] };
    }
    if (object.type.kind === "union") {
      const union = object.type.union!;
      if (ast.property === union.discriminant) {
        if (!options.allowDiscriminant) {
          this.reporter.error(
            ast.span,
            `the discriminant \`${union.discriminant}\` may only be compared with a string literal`,
          );
          return null;
        }
        return {
          kind: "ref",
          span: ast.span,
          type: { kind: "union", union, span: ast.span },
          args: [],
          slot: object.slot,
          sites: [],
          facts: [],
        };
      }
      const narrowing = object.slot === undefined ? undefined : narrowingOf(ctx, object.slot);
      const fieldType = narrowing?.variant?.fields.find((f) => f.name === ast.property);
      if (narrowing === undefined || narrowing.variant === null || narrowing.payload === null || fieldType === undefined) {
        this.reporter.error(
          ast.span,
          `the field \`${ast.property}\` of \`${union.name}\` needs a discriminant narrowing \`${union.discriminant}\``,
        );
        return null;
      }
      const payloadSlot: Slot = {
        kind: "payload",
        union,
        variant: narrowing.variant,
        payload: narrowing.payload,
      };
      const fieldExpr: ExprIR = {
        kind: "field",
        span: ast.span,
        type: fieldType.type,
        args: [object],
        slot: payloadSlot,
        union,
        variant: narrowing.variant,
        field: fieldType,
        sites: [],
        facts: [],
      };
      const facts: FactIR[] =
        fieldType.type.kind === "int" && fieldType.inRangePath !== undefined
          ? [
              {
                prop: goal("inRange", [fieldExpr], BOOL_TYPE(ast.span), ast.span),
                origin: "field-in-range",
                text: `InRange ${slotText(object.slot!)}.${ast.property}`,
              },
            ]
          : [];
      return { ...fieldExpr, facts };
    }
    this.reporter.error(
      ast.span,
      `\`${ast.property}\` is not a field of a union variant or \`length\` of a vector`,
    );
    return null;
  }

  private index(ast: A.IndexExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.optional) {
      this.reporter.error(ast.span, "optional chaining (`?.[]`) is not allowed in verified functions");
      return null;
    }
    const object = this.checkExpression(ast.object, ctx, env, {});
    const indexExpr = this.checkExpression(ast.index, ctx, env, {});
    if (object === null || indexExpr === null) return null;
    if (object.type.kind !== "vec" || object.vecLength === undefined) {
      this.reporter.error(ast.object.span, "only a `readonly T[]` value may be indexed");
      return null;
    }
    if (indexExpr.type.kind !== "int") {
      this.reporter.error(ast.index.span, "an array index must be a `number`");
      return null;
    }
    const elemType = object.type.elem!;
    const bounds = goal(
      "and",
      [
        this.le(this.intExpr(0n, ast.span), indexExpr, ast.span),
        this.lt(indexExpr, object.vecLength, ast.span),
      ],
      BOOL_TYPE(ast.span),
      ast.span,
    );
    const site = this.site("index", ast.span, ctx, bounds);
    const node: ExprIR = {
      kind: "index",
      span: ast.span,
      type: elemType,
      args: [object, indexExpr],
      siteId: site.id,
      sites: [site],
      facts: [],
    };
    if (elemType.kind !== "int") return node;
    // A `readonly number[]` read carries an `InRange` fact (section 6.3).  Its justification
    // is the runtime boundary guard, which checks every element; `fragment.ts` documents the
    // fact and milestone 7 applies the vector's `vec-elems` binder to the index proof.
    return {
      ...node,
      facts: [
        {
          prop: goal("inRange", [node], BOOL_TYPE(ast.span), ast.span),
          origin: "element-range",
          text: `InRange ${renderExpr(object)}[${renderExpr(indexExpr)}]`,
        },
      ],
    };
  }

  private unary(ast: A.UnaryExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.op === "+") return this.checkExpression(ast.operand, ctx, env, {});
    if (ast.op === "-") {
      const operand = this.checkExpression(ast.operand, ctx, env, {});
      if (operand === null) return null;
      if (operand.type.kind !== "int") {
        this.reporter.error(ast.span, "unary `-` needs a `number` operand");
        return null;
      }
      if (operand.kind === "int") {
        return this.intExpr(-(operand.literal as bigint), ast.span);
      }
      const node = goal("neg", [operand], INT_TYPE(ast.span), ast.span);
      const site = this.site("range", ast.span, ctx, this.inRange(node, ast.span));
      return { ...node, sites: [site] };
    }
    if (ast.op === "!") {
      const operand = this.checkExpression(ast.operand, ctx, env, { allowDiscriminant: true });
      if (operand === null) return null;
      if (operand.kind === "tagTest") {
        return { ...operand, literal: !(operand.literal === true) };
      }
      if (!isComparison(operand)) {
        this.reporter.error(ast.span, "`!` needs a condition operand");
        return null;
      }
      return goal("not", [operand], BOOL_TYPE(ast.span), ast.span);
    }
    if (ast.op === "~") {
      this.reporter.error(ast.span, "the bitwise operator `~` is not allowed in verified functions");
      return null;
    }
    this.reporter.error(ast.span, `\`${ast.op}\` is not allowed in verified functions`);
    return null;
  }

  private binary(ast: A.BinaryExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.op === "/") {
      this.reporter.error(
        ast.span,
        "`/` is only allowed as `Math.floor(e / k)` or `Math.trunc(e / k)` with a positive integer literal divisor",
      );
      return null;
    }
    if (ast.op === "%") {
      this.reporter.error(ast.span, "`%` is not allowed in verified functions");
      return null;
    }
    if (ast.op === "==" || ast.op === "!=") {
      this.reporter.error(ast.span, `\`${ast.op}\` is not allowed in verified functions; use \`===\` or \`!==\``);
      return null;
    }
    if (ast.op === "&" || ast.op === "|" || ast.op === "^" || ast.op === "<<" || ast.op === ">>" || ast.op === ">>>") {
      this.reporter.error(ast.span, `the bitwise operator \`${ast.op}\` is not allowed in verified functions`);
      return null;
    }
    if (ast.op === "**" || ast.op === "instanceof" || ast.op === "in") {
      this.reporter.error(ast.span, `\`${ast.op}\` is not allowed in verified functions`);
      return null;
    }
    if (ast.op === "===" || ast.op === "!==") {
      return this.equality(ast, ctx, env);
    }
    const left = this.checkExpression(ast.left, ctx, env, {});
    const right = this.checkExpression(ast.right, ctx, env, {});
    if (left === null || right === null) return null;
    if (left.type.kind !== "int" || right.type.kind !== "int") {
      this.reporter.error(ast.span, `\`${ast.op}\` needs two \`number\` operands in verified functions`);
      return null;
    }
    if (ast.op === "*") {
      const literal = left.kind === "int" ? left : right.kind === "int" ? right : null;
      const other = left.kind === "int" ? right : left;
      if (literal === null) {
        this.reporter.error(ast.span, "one side of `*` must be an integer literal in verified functions");
        return null;
      }
      if (other.kind === "int") {
        return this.intExpr((literal.literal as bigint) * (other.literal as bigint), ast.span);
      }
      const node = goal("mul", [literal, other], INT_TYPE(ast.span), ast.span);
      const site = this.site("range", ast.span, ctx, this.inRange(node, ast.span));
      return { ...node, sites: [site] };
    }
    if (ast.op === "+" || ast.op === "-") {
      if (left.kind === "int" && right.kind === "int") {
        const value = ast.op === "+" ? (left.literal as bigint) + (right.literal as bigint) : (left.literal as bigint) - (right.literal as bigint);
        return this.intExpr(value, ast.span);
      }
      const node = goal(ast.op === "+" ? "add" : "sub", [left, right], INT_TYPE(ast.span), ast.span);
      const site = this.site("range", ast.span, ctx, this.inRange(node, ast.span));
      return { ...node, sites: [site] };
    }
    if (ast.op === "<" || ast.op === "<=" || ast.op === ">" || ast.op === ">=") {
      const kind = ast.op === "<" ? "lt" : ast.op === "<=" ? "le" : ast.op === ">" ? "gt" : "ge";
      return goal(kind, [left, right], BOOL_TYPE(ast.span), ast.span);
    }
    this.reporter.error(ast.span, `\`${ast.op}\` is not allowed in verified functions`);
    return null;
  }

  private equality(ast: A.BinaryExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    const positive = ast.op === "===";
    // A discriminant test: `s.kind === "square"` (or with the operands swapped).
    const discriminant = this.discriminantTest(ast, ctx, env);
    if (discriminant !== null) return discriminant;
    const left = this.checkExpression(ast.left, ctx, env, {});
    const right = this.checkExpression(ast.right, ctx, env, {});
    if (left === null || right === null) return null;
    if (left.type.kind !== "int" || right.type.kind !== "int") {
      this.reporter.error(
        ast.span,
        `\`${ast.op}\` is only supported between two \`number\` values in verified functions`,
      );
      return null;
    }
    return goal(positive ? "eq" : "neq", [left, right], BOOL_TYPE(ast.span), ast.span);
  }

  private discriminantTest(ast: A.BinaryExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    const pairs: [A.Expr, A.Expr][] = [
      [ast.left, ast.right],
      [ast.right, ast.left],
    ];
    for (const [memberSide, literalSide] of pairs) {
      if (memberSide.kind !== "Member" || literalSide.kind !== "Lit" || literalSide.lit !== "string") continue;
      const object = this.checkExpression(memberSide.object, ctx, env, { allowDiscriminant: true });
      if (object === null || object.type.kind !== "union" || object.slot === undefined) continue;
      const union = object.type.union!;
      if (memberSide.property !== union.discriminant) continue;
      const tag = String(literalSide.value);
      const variant = union.variants.find((v) => v.tag === tag);
      if (variant === undefined) {
        this.reporter.error(literalSide.span, `\`${tag}\` is not a variant of \`${union.name}\``);
        return null;
      }
      return {
        kind: "tagTest",
        span: ast.span,
        type: BOOL_TYPE(ast.span),
        args: [],
        slot: object.slot,
        union,
        variant,
        literal: ast.op === "===",
        sites: [],
        facts: [],
      };
    }
    return null;
  }

  private logical(ast: A.LogicalExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.op === "??") {
      this.reporter.error(ast.span, "`??` is not allowed in verified functions");
      return null;
    }
    const left = this.checkExpression(ast.left, ctx, env, {});
    if (left === null) return null;
    if (left.type.kind !== "boolean") {
      this.reporter.error(ast.left.span, "the left side of a logical operator must be a condition");
      return null;
    }
    const right = this.checkExpression(ast.right, ctx, env, {});
    if (right === null) return null;
    if (right.type.kind !== "boolean") {
      this.reporter.error(ast.right.span, "the right side of a logical operator must be a condition");
      return null;
    }
    if (ast.op === "&&") {
      const bound = bind(ctx, "h", safePropTerm(ctx, left), "hypothesis", undefined, ast.span);
      return {
        kind: "and",
        span: ast.span,
        type: BOOL_TYPE(ast.span),
        args: [left, right],
        rightBinder: bound.binder,
        sites: [],
        facts: [],
      };
    }
    return {
      kind: "or",
      span: ast.span,
      type: BOOL_TYPE(ast.span),
      args: [left, right],
      sites: [],
      facts: [],
    };
  }

  private conditional(ast: A.CondExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    const condition = this.conditionWithScopes(ast.test, ctx, env);
    if (condition === null) return null;
    const consequent = this.checkExpression(ast.consequent, condition.thenCtx, env, {});
    const alternate = this.checkExpression(ast.alternate, condition.elseCtx, env, {});
    if (consequent === null || alternate === null) return null;
    if (!typesMatch(consequent.type, alternate.type)) {
      this.reporter.error(ast.span, "both branches of a ternary must have the same type");
      return null;
    }
    const cond = { ...condition.cond, thenExpr: consequent, elseExpr: alternate };
    return {
      kind: "cond",
      span: ast.span,
      type: consequent.type,
      args: [],
      cond,
      sites: [],
      facts: [],
    };
  }

  private arrayLiteral(ast: A.ArrayLit, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.elements.length === 0) {
      this.reporter.error(ast.span, "an array literal in a verified function must be `[...a, ...b]`");
      return null;
    }
    const parts: ExprIR[] = [];
    for (const element of ast.elements) {
      if (element.kind !== "Spread") {
        this.reporter.error(element.span, "an array literal in a verified function must be `[...a, ...b]`");
        return null;
      }
      const part = this.checkExpression(element.expr, ctx, env, {});
      if (part === null) return null;
      if (part.type.kind !== "vec" || part.vecLength === undefined) {
        this.reporter.error(element.span, "only `readonly T[]` values may be spread into an array literal");
        return null;
      }
      parts.push(part);
    }
    const first = parts[0]!;
    if (parts.some((part) => !typesMatch(first.type, part.type))) {
      this.reporter.error(ast.span, "all spread values must have the same element type");
      return null;
    }
    const length = parts
      .map((part) => part.vecLength!)
      .reduce((a, b) => goal("add", [a, b], INT_TYPE(ast.span), ast.span));
    const bound = goal(
      "le",
      [length, this.intExpr(K.MAX_VEC_LEN, ast.span)],
      BOOL_TYPE(ast.span),
      ast.span,
    );
    const site = this.site("append-length", ast.span, ctx, bound);
    return {
      kind: "append",
      span: ast.span,
      type: { kind: "vec", elem: first.type.elem!, span: ast.span },
      args: parts,
      vecLength: length,
      siteId: site.id,
      sites: [site],
      facts: [],
    };
  }

  private objectLiteral(ast: A.ObjectLit, ctx: Ctx, env: FnEnv, options: ExpressionOptions): ExprIR | null {
    const expected = options.expected;
    if (expected === undefined || expected === null || expected.kind !== "union") {
      this.reporter.error(ast.span, "an object literal is only allowed where a union variant is expected");
      return null;
    }
    const union = expected.union!;
    const props = new Map<string, A.ObjectProp>();
    for (const prop of ast.props) {
      if (prop.kind !== "Prop" || prop.keyKind !== "ident") {
        this.reporter.error(prop.span, "only plain `key: value` properties are allowed in a union variant literal");
        return null;
      }
      props.set(prop.keyText, prop);
    }
    const discriminant = props.get(union.discriminant);
    if (discriminant === undefined || discriminant.kind !== "Prop" || discriminant.value.kind !== "Lit") {
      this.reporter.error(ast.span, `the literal needs the discriminant \`${union.discriminant}\``);
      return null;
    }
    const tag = String(discriminant.value.value);
    const variant = union.variants.find((v) => v.tag === tag);
    if (variant === undefined) {
      this.reporter.error(discriminant.span, `\`${tag}\` is not a variant of \`${union.name}\``);
      return null;
    }
    const args: ExprIR[] = [];
    for (const field of variant.fields) {
      const prop = props.get(field.name);
      if (prop === undefined || prop.kind !== "Prop") {
        this.reporter.error(ast.span, `the variant \`${tag}\` needs the field \`${field.name}\``);
        return null;
      }
      const checked = this.checkExpression(prop.value, ctx, env, { expected: field.type });
      if (checked === null) return null;
      args.push(checked);
    }
    return {
      kind: "object",
      span: ast.span,
      type: expected,
      args,
      union,
      variant,
      sites: [],
      facts: [],
    };
  }

  // ---- calls ----------------------------------------------------------------

  private call(ast: A.CallExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.optional) {
      this.reporter.error(ast.span, "optional chaining (`?.()`) is not allowed in verified functions");
      return null;
    }
    if (ast.typeArgsText !== undefined) {
      this.reporter.error(ast.span, "explicit type arguments on a call are not in the verified fragment");
      return null;
    }
    if (ast.callee.kind === "Member") {
      const property = ast.callee.property;
      if (ARRAY_MUTATORS.has(property)) {
        this.reporter.error(
          ast.span,
          `array mutation (\`${property}\`) is not allowed in verified functions`,
        );
        return null;
      }
      if (property === "slice") return this.sliceCall(ast, ast.callee, ctx, env);
      return this.mathCall(ast, ctx, env);
    }
    if (ast.callee.kind !== "Ident") {
      // Check the callee anyway: an arrow function or a `new` expression inside it gets its
      // own, more precise diagnostic.
      if (this.checkExpression(ast.callee, ctx, env, {}) === null) return null;
      this.reporter.error(ast.callee.span, "only a named verified function may be called in verified functions");
      return null;
    }
    const name = ast.callee.name;
    const args: ExprIR[] = [];
    for (const arg of ast.args) {
      const checked = this.checkExpression(arg, ctx, env, {});
      if (checked === null) return null;
      args.push(checked);
    }
    if (name === this.fn.name) {
      this.recursive = true;
      const signature = this.signatureSummary;
      if (signature === null) return null;
      if (this.measure === null) {
        this.reporter.error(
          ast.span,
          `the recursive function \`${name}\` needs a \`@decreases\` tag`,
        );
      }
      return this.callWithSignature(ast, ctx, env, args, {
        kind: "self",
        name,
        signature,
        external: null,
      });
    }
    const local = this.localFunctions.get(name);
    if (local !== undefined) {
      return this.callWithSignature(ast, ctx, env, args, {
        kind: "local",
        name,
        signature: local,
        external: null,
      });
    }
    const imported = this.importedSpec(name, ast.callee.span);
    if (imported !== null) {
      return this.callWithSignature(ast, ctx, env, args, {
        kind: "imported",
        name,
        signature: imported.signature,
        external: imported,
      });
    }
    this.reporter.error(
      ast.callee.span,
      `\`${name}\` is not a verified function; calls to unverified functions are not allowed in verified functions`,
    );
    return null;
  }

  /** `a.slice(i, j)`: a `slice` site and a vector of length `j - i`. */
  private sliceCall(ast: A.CallExpr, member: A.MemberExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    if (ast.args.length !== 2) {
      this.reporter.error(ast.span, "`slice` takes exactly two arguments in verified functions");
      return null;
    }
    const object = this.checkExpression(member.object, ctx, env, {});
    const start = this.checkExpression(ast.args[0]!, ctx, env, {});
    const end = this.checkExpression(ast.args[1]!, ctx, env, {});
    if (object === null || start === null || end === null) return null;
    if (object.type.kind !== "vec" || object.vecLength === undefined) {
      this.reporter.error(member.object.span, "`slice` is only available on a `readonly T[]` value");
      return null;
    }
    if (start.type.kind !== "int" || end.type.kind !== "int") {
      this.reporter.error(ast.span, "`slice` bounds must be `number` values");
      return null;
    }
    const bounds = goal(
      "and",
      [
        this.le(this.intExpr(0n, ast.span), start, ast.span),
        goal(
          "and",
          [
            this.le(start, end, ast.span),
            this.le(end, object.vecLength, ast.span),
          ],
          BOOL_TYPE(ast.span),
          ast.span,
        ),
      ],
      BOOL_TYPE(ast.span),
      ast.span,
    );
    const site = this.site("slice", ast.span, ctx, bounds);
    return {
      kind: "slice",
      span: ast.span,
      type: object.type,
      args: [object, start, end],
      vecLength: goal("sub", [end, start], INT_TYPE(ast.span), ast.span),
      siteId: site.id,
      sites: [site],
      facts: [],
    };
  }

  private mathCall(ast: A.CallExpr, ctx: Ctx, env: FnEnv): ExprIR | null {
    const member = ast.callee as A.MemberExpr;
    if (member.optional) {
      this.reporter.error(ast.span, "optional chaining (`?.`) is not allowed in verified functions");
      return null;
    }
    if (member.object.kind !== "Ident" || member.object.name !== "Math") {
      if (this.checkExpression(member.object, ctx, env, {}) === null) return null;
      this.reporter.error(ast.span, "only the prelude's `Math.*` built-ins may be called in verified functions");
      return null;
    }
    const builtin = lookupMathBuiltin(`Math.${member.property}`);
    if (builtin === undefined) {
      this.reporter.error(
        ast.span,
        `\`Math.${member.property}\` is not in the verified prelude (allowed: Math.max, Math.min, Math.abs, Math.floor, Math.trunc)`,
      );
      return null;
    }
    if (builtin.division) {
      if (ast.args.length !== 1) {
        this.reporter.error(ast.span, `\`Math.${member.property}\` takes exactly one argument`);
        return null;
      }
      const division = ast.args[0]!;
      if (division.kind !== "Binary" || division.op !== "/") {
        this.reporter.error(
          ast.span,
          `\`Math.${member.property}\` is only allowed as \`Math.${member.property}(e / k)\` with a positive integer literal divisor`,
        );
        return null;
      }
      const numerator = this.checkExpression(division.left, ctx, env, {});
      if (numerator === null) return null;
      if (numerator.type.kind !== "int") {
        this.reporter.error(division.left.span, "the dividend must be a `number`");
        return null;
      }
      const divisor = division.right;
      if (divisor.kind !== "Lit" || (divisor.lit !== "int" && divisor.lit !== "hex")) {
        this.reporter.error(
          divisor.span,
          "the divisor must be a positive integer literal in the verified fragment",
        );
        return null;
      }
      const divisorValue = typeof divisor.value === "bigint" ? divisor.value : BigInt(divisor.value);
      if (divisorValue <= 0n) {
        this.reporter.error(divisor.span, "the divisor must be a positive integer literal");
        return null;
      }
      const divisorExpr = this.intExpr(divisorValue, divisor.span);
      const node: ExprIR = {
        kind: "call",
        span: ast.span,
        type: INT_TYPE(ast.span),
        args: [numerator, divisorExpr],
        callee: { kind: "prelude", name: builtin.name, builtin },
        layout: { shape: "int", valuePath: [] },
        sites: [],
        facts: [],
      };
      const rangeSite = this.site("range", ast.span, ctx, this.inRange(node, ast.span));
      return { ...node, sites: [rangeSite] };
    }
    if (ast.args.length !== builtin.arity) {
      this.reporter.error(ast.span, `\`${builtin.name}\` takes exactly ${builtin.arity} argument(s)`);
      return null;
    }
    const args: ExprIR[] = [];
    for (const arg of ast.args) {
      const checked = this.checkExpression(arg, ctx, env, {});
      if (checked === null) return null;
      if (checked.type.kind !== "int") {
        this.reporter.error(arg.span, `\`${builtin.name}\` needs \`number\` arguments`);
        return null;
      }
      args.push(checked);
    }
    const node: ExprIR = {
      kind: "call",
      span: ast.span,
      type: INT_TYPE(ast.span),
      args,
      callee: { kind: "prelude", name: builtin.name, builtin },
      layout: { shape: "int", valuePath: [] },
      sites: [],
      facts: [],
    };
    const rangeSite = this.site("range", ast.span, ctx, this.inRange(node, ast.span));
    return { ...node, sites: [rangeSite] };
  }

  private callWithSignature(
    ast: A.CallExpr,
    ctx: Ctx,
    env: FnEnv,
    args: readonly ExprIR[],
    target: {
      kind: "local" | "self" | "imported";
      name: string;
      signature: SignatureIR;
      external: ImportedSpec | null;
    },
  ): ExprIR | null {
    const signature = target.signature;
    const valueBinders = signature.binders.filter((b) => b.role === "param" || b.role === "type-param");
    const params = valueBinders.filter((b) => b.role === "param");
    if (params.length !== args.length) {
      this.reporter.error(
        ast.span,
        `\`${target.name}\` takes ${params.length} argument(s), but ${args.length} were given`,
      );
      return null;
    }
    // Instantiate the callee's preconditions: parameters become the argument expressions and
    // vector lengths become the arguments' lengths.
    const substitution = new Map<number, ExprIR>();
    params.forEach((param, index) => {
      const arg = args[index]!;
      substitution.set(param.id, arg);
      const components = signature.binders.filter(
        (b) => b.role === "vec-len" && b.name === `n_${param.name}`,
      );
      const length = components[0];
      if (length !== undefined && arg.vecLength !== undefined) substitution.set(length.id, arg.vecLength);
    });
    const preParts: ExprIR[] = [];
    for (const pre of signature.preconditions) {
      const instantiated = substituteExpr(pre.prop, (e) => {
        if (e.kind !== "ref" || e.slot?.kind !== "binder") return null;
        return substitution.get(e.slot.binder.id) ?? null;
      });
      if (instantiated !== null) preParts.push(instantiated);
    }
    const preGoal = preParts.length === 0 ? this.trueExpr(ast.span) : this.conjoin(preParts, ctx, env, ast.span);
    const site = this.site("pre-call", ast.span, ctx, preGoal);
    const sites: ObligationSite[] = [site];
    if (target.kind === "self") {
      if (this.measure !== null) {
        const measure = this.measure;
        sites.push(
          this.site(
            "measure-nonneg",
            ast.span,
            ctx,
            this.le(this.intExpr(0n, ast.span), substituteParams(measure, substitution, args), ast.span),
          ),
        );
        sites.push(
          this.site(
            "measure-decrease",
            ast.span,
            ctx,
            this.lt(substituteParams(measure, substitution, args), measure, ast.span),
          ),
        );
      }
    }
    const resultType = signature.result.type;
    const node: ExprIR = {
      kind: "call",
      span: ast.span,
      type: resultType,
      args: [...args],
      callee:
        target.kind === "imported"
          ? { kind: "imported", name: target.name, imported: target.external! }
          : { kind: target.kind, name: target.name, fn: this.selfFunction },
      layout: signature.result.layout,
      sites,
      facts: [],
    };
    let out = node;
    if (resultType.kind === "vec") {
      const lengthPath = signature.result.layout.lengthPath ?? [0];
      out = {
        ...out,
        vecLength: {
          kind: "projection",
          span: ast.span,
          type: INT_TYPE(ast.span),
          args: [out],
          projPath: lengthPath,
          sites: [],
          facts: [],
        },
      };
    }
    if (resultType.kind === "int" && signature.result.layout.inRangePath !== undefined) {
      out = {
        ...out,
        facts: [
          {
            prop: goal("inRange", [out], BOOL_TYPE(ast.span), ast.span),
            origin: "call-result",
            text: `InRange ${target.name}(...)`,
          },
        ],
      };
    }
    return out;
  }

  // ---- imports --------------------------------------------------------------

  private importedSpec(name: string, span: Span): ImportedSpec | null {
    const cached = this.tables.importedSpecs.get(name);
    if (cached !== undefined) return cached;
    const binding = this.tables.importBindings.get(name);
    if (binding === undefined) return null;
    const resolved = this.tables.resolver.resolve(this.tables.path, binding.specifier);
    if (!resolved.ok) {
      this.reporter.error(span, resolved.message);
      this.tables.importedSpecs.set(name, null);
      return null;
    }
    this.tables.importedHashes.set(resolved.file.path, resolved.file.hash);
    const decl = specFunction(resolved.file.parsed, binding.imported);
    if (decl === undefined) {
      this.reporter.error(
        span,
        `\`${binding.imported}\` is not a verified function in \`${binding.specifier}\``,
      );
      this.tables.importedSpecs.set(name, null);
      return null;
    }
    const importedTables = tablesFor(this.session, resolved.file);
    const inner = new Reporter();
    const typeParams = new Set(decl.typeParams.map((tp) => tp.name));
    const built = buildSignature(this.session, importedTables, inner, decl, typeParams, this.session.ids);
    if (built === null) {
      const first = inner.diagnostics[0];
      this.reporter.error(
        span,
        `cannot use the spec of \`${name}\` from \`${binding.specifier}\`${first === undefined ? "" : `: ${first.message}`}`,
      );
      this.tables.importedSpecs.set(name, null);
      return null;
    }
    const spec: ImportedSpec = {
      name,
      file: resolved.file.path,
      hash: resolved.file.hash,
      signature: built.signature,
      decl: externalDeclFor(name, built.signature.type, resolved.file),
    };
    this.imports.push(spec);
    this.tables.importedSpecs.set(name, spec);
    return spec;
  }

  // ---- the function body ----------------------------------------------------

  run(build: SignatureBuild): FunctionIR | null {
    this.resultSummary = build.signature.result;
    const env = envOfParams(build.params);
    this.measure = this.measureExpression(build.ctx, env);
    const top: Continuation = () => {
      this.reporter.error(this.fn.span, `not every path through \`${this.fn.name}\` ends in a \`return\``);
      return [];
    };
    const body = this.walk(
      this.fn.body.body,
      build.ctx,
      env,
      top,
      null,
    );
    return {
      name: this.fn.name,
      span: this.fn.span,
      nameSpan: this.fn.nameSpan,
      exported: this.fn.exported,
      typeParams: build.signature.binders.filter((b) => b.role === "type-param"),
      params: [...build.params],
      signature: build.signature,
      measure: this.measure ?? undefined,
      recursive: this.recursive,
      body,
      loops: this.loops,
      sites: this.sites,
      imports: this.imports,
    };
  }

  measure: ExprIR | null = null;
  selfFunction: FunctionIR | null = null;
  signatureSummary: SignatureIR | null = null;
  private localFunctions = new Map<string, SignatureIR>();

  setLocalFunctions(functions: ReadonlyMap<string, SignatureIR>): void {
    this.localFunctions = new Map(functions);
  }

  private measureExpression(ctx: Ctx, env: FnEnv): ExprIR | null {
    const tags = this.fn.jsdoc === null ? [] : tagsNamed(this.fn.jsdoc, "decreases");
    if (tags.length === 0) return null;
    if (tags.length > 1) this.reporter.error(tags[1]!.span, "a function may have only one `@decreases` tag");
    const ast = this.parseTag(tags[0]!);
    if (ast === null) return null;
    const checked = this.checkExpression(ast, ctx, env, {});
    if (checked === null) return null;
    if (checked.type.kind !== "int") {
      this.reporter.error(tags[0]!.textSpan, "`@decreases` must be a non-negative integer expression");
      return null;
    }
    return checked;
  }
}

// ---------------------------------------------------------------------------
// Environment and substitution helpers
// ---------------------------------------------------------------------------

/** Substitute parameters in a callee's measure expression with the call's arguments. */
function substituteParams(
  measure: ExprIR,
  substitution: ReadonlyMap<number, ExprIR>,
  args: readonly ExprIR[],
): ExprIR {
  const replaced = substituteExpr(measure, (e) => {
    if (e.kind !== "ref" || e.slot?.kind !== "binder") return null;
    return substitution.get(e.slot.binder.id) ?? null;
  });
  return replaced === measure && args.length > 0 ? measure : replaced;
}

/** Structural type compatibility for the fragment's types. */
function typesMatch(a: TypeIR, b: TypeIR): boolean {
  if (a.kind !== b.kind) return false;
  if (a.kind === "vec") return typesMatch(a.elem!, b.elem!);
  if (a.kind === "union") return a.union!.name === b.union!.name && a.union!.file === b.union!.file;
  if (a.kind === "generic") return a.typeParam === b.typeParam;
  return true;
}

/**
 * Replace sub-expressions of `expr` whose `ref` slot holds a binder in `substitution`.
 * Used to instantiate a callee's preconditions and measure at a call site.
 */
export function substituteExpr(
  expr: ExprIR,
  replace: (e: ExprIR) => ExprIR | null,
): ExprIR {
  const direct = replace(expr);
  if (direct !== null) return direct;
  const args = expr.args.map((arg) => substituteExpr(arg, replace));
  const vecLength = expr.vecLength === undefined ? undefined : substituteExpr(expr.vecLength, replace);
  const cond =
    expr.cond === undefined
      ? undefined
      : {
          ...expr.cond,
          thenExpr: expr.cond.thenExpr === undefined ? undefined : substituteExpr(expr.cond.thenExpr, replace),
          elseExpr: expr.cond.elseExpr === undefined ? undefined : substituteExpr(expr.cond.elseExpr, replace),
        };
  const sites = expr.sites.map((site) => ({
    ...site,
    goal: substituteExpr(site.goal, replace),
    resultValue: site.resultValue === undefined ? undefined : substituteExpr(site.resultValue, replace),
  }));
  if (
    args.every((arg, i) => arg === expr.args[i]) &&
    vecLength === expr.vecLength &&
    cond === expr.cond &&
    sites.every((site, i) => site === expr.sites[i])
  ) {
    return expr;
  }
  return { ...expr, args, vecLength, cond, sites };
}

export function tagFact(test: TagTestIR, prop: ExprIR): FactIR {
  return {
    prop,
    origin: "tag-test",
    text: `${slotText(test.subject)}.${test.union.discriminant} === ${JSON.stringify(test.variant.tag)}`,
  };
}

/** Rewrite `if (a && b) T else E` into nested `if`s so every condition is a single test. */
export function normalizeIf(stmt: A.IfStmt): A.IfStmt {
  const test = stmt.test;
  if (test.kind === "Logical" && test.op === "&&") {
    const inner: A.IfStmt = {
      kind: "If",
      test: test.right,
      then: stmt.then,
      alternate: stmt.alternate,
      span: stmt.span,
    };
    const block: A.BlockStmt = { kind: "Block", body: [inner], span: stmt.span };
    return normalizeIf({ kind: "If", test: test.left, then: block, alternate: stmt.alternate, span: stmt.span });
  }
  if (test.kind === "Logical" && test.op === "||") {
    const inner: A.IfStmt = {
      kind: "If",
      test: test.right,
      then: stmt.then,
      alternate: stmt.alternate,
      span: stmt.span,
    };
    const block: A.BlockStmt = { kind: "Block", body: [inner], span: stmt.span };
    return normalizeIf({ kind: "If", test: test.left, then: stmt.then, alternate: block, span: stmt.span });
  }
  if (test.kind === "Unary" && test.op === "!") {
    return normalizeIf({
      kind: "If",
      test: test.operand,
      then: stmt.alternate ?? { kind: "Block", body: [], span: stmt.span },
      alternate: stmt.then,
      span: stmt.span,
    });
  }
  return stmt;
}

// ===========================================================================
// 7. Entry points
// ===========================================================================

interface Session {
  readonly resolver: SpecResolver;
  readonly tables: Map<string, FileTables>;
  readonly ids: Ids;
}

/** The file-level tables for one file: its unions, aliases, functions and imports. */
function tablesFor(session: Session, file: { path: string; source: string; parsed: A.ParsedFile }): FileTables {
  const cached = session.tables.get(file.path);
  if (cached !== undefined) return cached;
  const reporter = new Reporter();
  const unions = new Map<string, UnionIR>();
  const aliases = new Map<string, A.TypeAliasDecl>();
  for (const alias of file.parsed.typeAliases) {
    aliases.set(alias.name, alias);
    if (unions.has(alias.name)) continue;
    const union = buildUnion(alias, file.path, (span, message) => reporter.error(span, message));
    if (union !== null) unions.set(alias.name, union);
  }
  const functions = new Map<string, A.FnDecl>();
  for (const fn of file.parsed.functions) functions.set(fn.name, fn);
  const importBindings = new Map<string, { imported: string; specifier: string; span: Span }>();
  for (const decl of file.parsed.imports) {
    for (const binding of decl.bindings) {
      importBindings.set(binding.local, {
        imported: binding.imported,
        specifier: decl.specifier,
        span: binding.span,
      });
    }
  }
  const tables: FileTables = {
    diagnostics: reporter.diagnostics,
    path: file.path,
    source: file.source,
    resolver: session.resolver,
    unions,
    aliases,
    functions,
    importBindings,
    importedAliasCache: new Map(),
    importedSpecs: new Map(),
    importedHashes: new Map(),
  };
  session.tables.set(file.path, tables);
  return tables;
}

export interface ExtractOptions {
  /** File reader for imported specs; defaults to `node:fs.readFileSync`. */
  readonly readFile?: (path: string) => string;
  /** A pre-built resolver (tests reuse it across calls). */
  readonly resolver?: SpecResolver;
  /** The parsed file, when the caller already parsed it. */
  readonly parsed?: A.ParsedFile;
}

/**
 * Check one file: parse it (unless the caller already did), resolve its unions and names,
 * check every annotated function against the fragment, map its signature to a kernel type and
 * return the IR.  Never throws on bad input inside an annotated function; every problem is a
 * located diagnostic.
 */
export function extractFile(path: string, source: string, options: ExtractOptions = {}): FileIR {
  const reporter = new Reporter();
  const resolver = options.resolver ?? new SpecResolver(options.readFile);
  const session: Session = { resolver, tables: new Map(), ids: new Ids() };
  const parsed = options.parsed ?? parseFile(path, source);
  reporter.diagnostics.push(...parsed.diagnostics);

  const tables = tablesFor(session, { path, source, parsed });
  reporter.diagnostics.push(...tables.diagnostics);
  const typeParamsByFunction = new Map<string, Set<string>>();
  for (const fn of parsed.functions) {
    typeParamsByFunction.set(fn.name, new Set(fn.typeParams.map((tp) => tp.name)));
  }

  // Pass 1: every signature (so calls and recursion resolve).
  const signatures = new Map<string, SignatureBuild>();
  for (const fn of parsed.functions) {
    const built = guard(reporter, fn, () =>
      buildSignature(session, tables, reporter, fn, typeParamsByFunction.get(fn.name)!, session.ids),
    );
    if (built !== null && built !== undefined) signatures.set(fn.name, built);
  }

  // Pass 2: every body.
  const functions: FunctionIR[] = [];
  for (const fn of parsed.functions) {
    const built = signatures.get(fn.name);
    if (built === undefined) continue;
    const checker = new FnChecker(
      session,
      tables,
      reporter,
      fn,
      typeParamsByFunction.get(fn.name)!,
      built.ctx,
      built.signature.result.term,
    );
    checker.signatureSummary = built.signature;
    const locals = new Map<string, SignatureIR>();
    for (const [name, other] of signatures) {
      if (name !== fn.name) locals.set(name, other.signature);
    }
    checker.setLocalFunctions(locals);
    const result = guard(reporter, fn, () => checker.run(built));
    if (result === null || result === undefined) continue;
    const functionIr: FunctionIR = { ...result, signature: built.signature };
    checker.selfFunction = functionIr;
    functions.push(functionIr);
  }

  const usedImports = new Map<string, string>();
  for (const fn of functions) {
    for (const spec of fn.imports) usedImports.set(spec.file, spec.hash);
  }
  for (const [file, hash] of tables.importedHashes) usedImports.set(file, hash);

  return {
    path,
    source,
    functions,
    unions: [...tables.unions.values()],
    importedHashes: usedImports,
    diagnostics: dedupe(sortDiagnostics(reporter.diagnostics)),
  };
}

/**
 * Run one extraction step for one function, turning any failure into a located `internal`
 * diagnostic.  Extraction must never throw on user input (section 2, hard rules): a crash in
 * the untrusted layer is reported like any other problem instead of stopping the build.
 */
function guard<T>(
  reporter: Reporter,
  fn: A.FnDecl,
  run: () => T,
): T | null {
  try {
    return run();
  } catch (error) {
    const detail = error instanceof Error ? error.message : String(error);
    reporter.diagnostics.push({
      kind: "internal",
      severity: "error",
      span: fn.nameSpan,
      message: `could not extract \`${fn.name}\`: ${detail}`,
    });
    return null;
  }
}

/** Deterministic diagnostics without duplicates from a spec checked twice. */
function dedupe(diagnostics: readonly Diagnostic[]): Diagnostic[] {
  const out: Diagnostic[] = [];
  const seen = new Set<string>();
  for (const diagnostic of diagnostics) {
    const key = `${diagnostic.kind}|${diagnostic.span.file}|${diagnostic.span.offset}|${diagnostic.span.endOffset ?? ""}|${diagnostic.message}`;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push(diagnostic);
  }
  return out;
}


