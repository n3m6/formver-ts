/**
 * The kernel's public API (specification section 6.1.6).
 *
 * Everything the untrusted layers need is here: the term language and its constructors,
 * the built-in names, the environment, and the checking entry points. Nothing outside
 * `src/kernel/` may import a kernel module other than this one.
 */
import {
  AND_NAME,
  IN_RANGE_NAME,
  LT_NAME,
  MAX_VEC_LEN,
  NOT_NAME,
  OP_ABSURD,
  OP_ADD,
  OP_APPEND,
  OP_BY_CONTRA,
  OP_CASE,
  OP_CAST_VEC,
  OP_DIV_FLOOR,
  OP_DIV_FLOOR_SPEC,
  OP_DIV_TRUNC,
  OP_DIV_TRUNC_SPEC_NEG,
  OP_DIV_TRUNC_SPEC_NONNEG,
  OP_EMPTY,
  OP_EQ,
  OP_FIX_WF,
  OP_GET,
  OP_IF_LE,
  OP_INL,
  OP_INR,
  OP_INT,
  OP_INT_EQ,
  OP_J,
  OP_LE,
  OP_LEN,
  OP_MUL_CONST,
  OP_NEG,
  OP_REFL,
  OP_SLICE,
  OP_SUB,
  OP_SUM,
  OP_TT,
  OP_UNIT,
  OP_VEC,
  OP_VEC_BOUNDS,
  SAFE_MAX,
  leProofTerm,
} from "./builtins";
import { app, appMany, constTerm, farkasTerm, intLit, primTerm, type Level, type PrimOp, type Term } from "./term";

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type { Term, Level, PrimOp, ErasedTerm, Mk } from "./term";
export type { Decl, Env, DefDecl, AxiomDecl, ExternalDecl } from "./env";
export type { KernelError, KernelErrorReason, Result } from "./errors";
export type { Value, Closure, Head, NeutralValue, PrimInfo, ReduceCtx, GlobalInfo, LinearAtom, LinearValue, LinearForm } from "./value";
export type { Ctx } from "./check";
export type { Row, FarkasRule } from "./farkas";
export type { IrrelevantOf } from "./linear";

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

export { emptyEnv, addDecl, lookupDecl, axiomsUsed, externalsUsed } from "./env";

// ---------------------------------------------------------------------------
// Checking
// ---------------------------------------------------------------------------

export { inferType, checkType, isTypeTerm, infer, check, emptyCtx } from "./check";
export { isConvertible, convValue, convPrimArgs } from "./conv";
export { normalize, quote } from "./quote";
export { evalTerm } from "./eval";

// ---------------------------------------------------------------------------
// Built-ins
// ---------------------------------------------------------------------------

export {
  PRIMS,
  lookupPrim,
  irrelevantOf,
  leProofTerm,
  OP_EMPTY,
  OP_UNIT,
  OP_TT,
  OP_SUM,
  OP_INL,
  OP_INR,
  OP_CASE,
  OP_ABSURD,
  OP_EQ,
  OP_REFL,
  OP_J,
  OP_INT,
  OP_ADD,
  OP_SUB,
  OP_NEG,
  OP_MUL_CONST,
  OP_LE,
  OP_IF_LE,
  OP_BY_CONTRA,
  OP_INT_EQ,
  OP_VEC,
  OP_LEN,
  OP_VEC_BOUNDS,
  OP_GET,
  OP_APPEND,
  OP_SLICE,
  OP_CAST_VEC,
  OP_FIX_WF,
  OP_DIV_FLOOR,
  OP_DIV_FLOOR_SPEC,
  OP_DIV_TRUNC,
  OP_DIV_TRUNC_SPEC_NONNEG,
  OP_DIV_TRUNC_SPEC_NEG,
  AND_NAME,
  NOT_NAME,
  LT_NAME,
  IN_RANGE_NAME,
  SAFE_MAX,
  MAX_VEC_LEN,
} from "./builtins";
export { checkFarkas, rowOfLe, tightenRow, checkCertificate, floorDiv, gcd } from "./farkas";
export {
  emptyForm,
  formAdd,
  formEquals,
  formNeg,
  formOf,
  formScale,
  formSub,
  formKeyText,
  keyOfValue,
  truncDiv,
  vform,
} from "./linear";
export { vint, vlinear, vvar, vprim } from "./value";

// ---------------------------------------------------------------------------
// Terms and printing
// ---------------------------------------------------------------------------

export {
  varTerm,
  sort,
  pi,
  lam,
  app,
  appMany,
  sigma,
  pair,
  fst,
  snd,
  letTerm,
  let_,
  constTerm,
  intLit,
  primTerm,
  farkasTerm,
  erase,
  formatTerm,
  mk,
  Scope,
  varMk,
  sortMk,
  constMk,
  intLitMk,
  appMk,
  appManyMk,
  primMk,
  piMk,
  lamMk,
  sigmaMk,
  letMk,
  pairMk,
  farkasMk,
  fstMk,
  sndMk,
} from "./term";

export { ok, err, kernelError, formatKernelError, KernelInternalError } from "./errors";

// ---------------------------------------------------------------------------
// Built-in term constructors
//
// Milestone 3 note: `Vec` and `InRange` are exported now so that the elaborator can be
// written against the final surface; until their registry entry (`Vec`) and definition
// (`InRange`) land, checking a term that mentions them fails with `unknown-prim` or
// `unbound-constant`. That is the intended, reported behaviour, never a silent one.
// ---------------------------------------------------------------------------

/** `add a b : Int`; both sides normalize to a linear value. */
export const Add = (a: Term, b: Term): Term => primTerm(OP_ADD, [a, b]);
/** `sub a b : Int`. */
export const Sub = (a: Term, b: Term): Term => primTerm(OP_SUB, [a, b]);
/** `neg a : Int`. */
export const Neg = (a: Term): Term => primTerm(OP_NEG, [a]);
/** `mulConst k e : Int`, with `k` a literal (specification 6.1.3). */
export const MulConst = (k: Term, e: Term): Term => primTerm(OP_MUL_CONST, [k, e]);
/** `Lt a b`, the definition `Le (a + 1) b`. */
export const Lt = (a: Term, b: Term): Term => app(app(constTerm(LT_NAME), a), b);
/** `ifLe {level} A a b yes no : A`; reduces when `a` and `b` are literals. */
export const IfLe = (
  level: Level,
  result: Term,
  lhs: Term,
  rhs: Term,
  yes: Term,
  no: Term,
): Term => primTerm(OP_IF_LE, [result, lhs, rhs, yes, no], level);
/** `byContra a b (k : Lt b a -> Empty) : Le a b`. */
export const ByContra = (a: Term, b: Term, k: Term): Term => primTerm(OP_BY_CONTRA, [a, b, k]);
/** `intEq a b (p : Le a b) (q : Le b a) : Eq Int a b`. */
export const IntEq = (a: Term, b: Term, p: Term, q: Term): Term => primTerm(OP_INT_EQ, [a, b, p, q]);
/** `LeProof x y : Le x y` for literal `x <= y`: `byContra` plus a one-hypothesis Farkas. */
export const LeProof = (x: bigint | number, y: bigint | number): Term =>
  leProofTerm(typeof x === "bigint" ? x : BigInt(x), typeof y === "bigint" ? y : BigInt(y));
/** `len A n v : Int`, which reduces to `n`. */
export const Len = (a: Term, n: Term, v: Term): Term => primTerm(OP_LEN, [a, n, v]);
/** `vecBounds A n v : And (Le 0 n) (Le n 4294967295)`, a primitive lemma. */
export const VecBounds = (a: Term, n: Term, v: Term): Term => primTerm(OP_VEC_BOUNDS, [a, n, v]);
/** `get A n v i p : A`, with `p : And (Le 0 i) (Lt i n)`. */
export const Get = (a: Term, n: Term, v: Term, i: Term, p: Term): Term =>
  primTerm(OP_GET, [a, n, v, i, p]);
/** `append A n m u w p : Vec A (n + m)`, with `p : Le (n + m) 4294967295`. */
export const Append = (a: Term, n: Term, m: Term, u: Term, w: Term, p: Term): Term =>
  primTerm(OP_APPEND, [a, n, m, u, w, p]);
/** `slice A n v i j p : Vec A (j - i)`, with `p : And (Le 0 i) (And (Le i j) (Le j n))`. */
export const Slice = (a: Term, n: Term, v: Term, i: Term, j: Term, p: Term): Term =>
  primTerm(OP_SLICE, [a, n, v, i, j, p]);
/** `castVec A n m e v : Vec A m` for `e : Eq Int n m`. */
export const CastVec = (a: Term, n: Term, m: Term, e: Term, v: Term): Term =>
  primTerm(OP_CAST_VEC, [a, n, m, e, v]);
/** `fixWf {level} A B m step x p : B x`; opaque, it never unfolds. */
export const FixWf = (
  level: Level,
  a: Term,
  b: Term,
  measure: Term,
  step: Term,
  x: Term,
  p: Term,
): Term => primTerm(OP_FIX_WF, [a, b, measure, step, x, p], level);
/** `divFloor e k : Int` for a positive literal `k`. */
export const DivFloor = (e: Term, k: Term): Term => primTerm(OP_DIV_FLOOR, [e, k]);
/** `divFloorSpec e k : And (Le (k*q) e) (Le e (k*q + k - 1))`, `q = divFloor e k`. */
export const DivFloorSpec = (e: Term, k: Term): Term => primTerm(OP_DIV_FLOOR_SPEC, [e, k]);
/** `divTrunc e k : Int` for a positive literal `k`. */
export const DivTrunc = (e: Term, k: Term): Term => primTerm(OP_DIV_TRUNC, [e, k]);
/** `divTruncSpecNonneg e k (h : Le 0 e)`, where `q = divTrunc e k`: `k*q <= e <= k*q + k - 1`. */
export const DivTruncSpecNonneg = (e: Term, k: Term, h: Term): Term =>
  primTerm(OP_DIV_TRUNC_SPEC_NONNEG, [e, k, h]);
/** `divTruncSpecNeg e k (h : Lt e 0)`, where `q = divTrunc e k`: `k*q - k + 1 <= e <= k*q`. */
export const DivTruncSpecNeg = (e: Term, k: Term, h: Term): Term =>
  primTerm(OP_DIV_TRUNC_SPEC_NEG, [e, k, h]);

/** `Empty : Type 0`. */
export const Empty: Term = primTerm(OP_EMPTY, []);
/** `Unit : Type 0`. */
export const Unit: Term = primTerm(OP_UNIT, []);
/** `tt : Unit`. */
export const tt: Term = primTerm(OP_TT, []);
/** `Int : Type 0` (milestone 3 adds its operations and linear normal forms). */
export const Int: Term = primTerm(OP_INT, []);

export const Sum = (a: Term, b: Term): Term => primTerm(OP_SUM, [a, b]);
export const Inl = (a: Term, b: Term, x: Term): Term => primTerm(OP_INL, [a, b, x]);
export const Inr = (a: Term, b: Term, x: Term): Term => primTerm(OP_INR, [a, b, x]);
export const SumCase = (
  level: number,
  a: Term,
  b: Term,
  motive: Term,
  onLeft: Term,
  onRight: Term,
  scrutinee: Term,
): Term => primTerm(OP_CASE, [a, b, motive, onLeft, onRight, scrutinee], level);

export const Absurd = (level: number, a: Term, empty: Term): Term => primTerm(OP_ABSURD, [a, empty], level);
export const Eq = (a: Term, x: Term, y: Term): Term => primTerm(OP_EQ, [a, x, y]);
export const Refl = (a: Term, x: Term): Term => primTerm(OP_REFL, [a, x]);
export const J = (
  level: number,
  a: Term,
  x: Term,
  motive: Term,
  base: Term,
  b: Term,
  proof: Term,
): Term => primTerm(OP_J, [a, x, motive, base, b, proof], level);

/** `And A B`, the non-dependent `Sigma`; a prelude definition, so it unfolds by delta. */
export const And = (a: Term, b: Term): Term => app(app(constTerm(AND_NAME), a), b);
/** `Not A`, that is `A -> Empty`; a prelude definition. */
export const Not = (a: Term): Term => app(constTerm(NOT_NAME), a);
/** `Le a b : Type 0`, the primitive proposition. */
export const Le = (a: Term, b: Term): Term => primTerm(OP_LE, [a, b]);
/** `Vec A n : Type 0` (milestone 3 registers the op). */
export const Vec = (a: Term, n: Term): Term => primTerm(OP_VEC, [a, n]);
/** `InRange x` (milestone 3 adds the definition). */
export const InRange = (x: Term): Term => app(constTerm(IN_RANGE_NAME), x);
/** `Farkas { hyps, coeffs } : Empty` when the certificate checks. */
export const Farkas = (hyps: readonly Term[], coeffs: readonly bigint[]): Term => farkasTerm(hyps, coeffs);
