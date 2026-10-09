/**
 * The kernel's public API (specification section 6.1.6).
 *
 * Everything the untrusted layers need is here: the term language and its constructors,
 * the built-in names, the environment, and the checking entry points. Nothing outside
 * `src/kernel/` may import a kernel module other than this one.
 */
import { AND_NAME, NOT_NAME, OP_ABSURD, OP_CASE, OP_EMPTY, OP_EQ, OP_INT, OP_INL, OP_INR, OP_J, OP_LE, OP_REFL, OP_SUM, OP_TT, OP_UNIT, OP_VEC, IN_RANGE_NAME } from "./builtins";
import { app, appMany, constTerm, farkasTerm, intLit, primTerm, type PrimOp, type Term } from "./term";

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export type { Term, Level, PrimOp, ErasedTerm, Mk } from "./term";
export type { Decl, Env, DefDecl, AxiomDecl, ExternalDecl } from "./env";
export type { KernelError, KernelErrorReason, Result } from "./errors";
export type { Value, Closure, Head, NeutralValue, PrimInfo, ReduceCtx, GlobalInfo } from "./value";
export type { Ctx } from "./check";
export type { Row, FarkasRule } from "./farkas";

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

export { PRIMS, lookupPrim, OP_EMPTY, OP_UNIT, OP_TT, OP_SUM, OP_INL, OP_INR, OP_CASE, OP_ABSURD, OP_EQ, OP_REFL, OP_J, OP_INT, OP_LE, OP_VEC, AND_NAME, NOT_NAME, IN_RANGE_NAME } from "./builtins";
export { checkFarkas, tightenRow, checkCertificate, floorDiv, gcd } from "./farkas";

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
