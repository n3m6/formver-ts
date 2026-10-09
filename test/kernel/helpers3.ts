/**
 * Shared term fixtures for the milestone-3 kernel tests (integers, `Le`/Farkas, vectors,
 * `fixWf`, division). Everything is built with the public builder, exactly as the
 * untrusted elaborator will build it.
 */
import * as K from "../../src/kernel/index";

export const env = K.emptyEnv();

// ---------------------------------------------------------------------------
// Type-level builders (`Mk`): for terms with binders
// ---------------------------------------------------------------------------

export const intMk: K.Mk = () => K.Int;
export const emptyMk: K.Mk = () => K.Empty;
export const sort0Mk: K.Mk = K.sortMk(0);
export const v = (name: string): K.Mk => K.varMk(name);

export const addMk = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_ADD, [a, b]);
export const subMk = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_SUB, [a, b]);
export const negMk = (a: K.Mk): K.Mk => K.primMk(K.OP_NEG, [a]);
export const mulConstMk = (k: bigint | K.Mk, e: K.Mk): K.Mk => {
  const literal = typeof k === "bigint" ? K.intLitMk(k) : k;
  return K.primMk(K.OP_MUL_CONST, [literal, e]);
};

export const leMk = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_LE, [a, b]);
export const ltMk = (a: K.Mk, b: K.Mk): K.Mk => K.appManyMk(K.constMk(K.LT_NAME), [a, b]);
export const andMk = (a: K.Mk, b: K.Mk): K.Mk => K.appManyMk(K.constMk(K.AND_NAME), [a, b]);
export const inRangeMk = (x: K.Mk): K.Mk => K.appMk(K.constMk(K.IN_RANGE_NAME), x);
export const eqMk = (a: K.Mk, x: K.Mk, y: K.Mk): K.Mk => K.primMk(K.OP_EQ, [a, x, y]);
export const vecMk = (a: K.Mk, n: K.Mk): K.Mk => K.primMk(K.OP_VEC, [a, n]);
export const lenMk = (a: K.Mk, n: K.Mk, vec: K.Mk): K.Mk => K.primMk(K.OP_LEN, [a, n, vec]);
export const vecBoundsMk = (a: K.Mk, n: K.Mk, vec: K.Mk): K.Mk => K.primMk(K.OP_VEC_BOUNDS, [a, n, vec]);
export const getMk = (a: K.Mk, n: K.Mk, vec: K.Mk, i: K.Mk, p: K.Mk): K.Mk =>
  K.primMk(K.OP_GET, [a, n, vec, i, p]);
export const appendMk = (a: K.Mk, n: K.Mk, m: K.Mk, u: K.Mk, w: K.Mk, p: K.Mk): K.Mk =>
  K.primMk(K.OP_APPEND, [a, n, m, u, w, p]);
export const sliceMk = (a: K.Mk, n: K.Mk, vec: K.Mk, i: K.Mk, j: K.Mk, p: K.Mk): K.Mk =>
  K.primMk(K.OP_SLICE, [a, n, vec, i, j, p]);
export const castVecMk = (a: K.Mk, n: K.Mk, m: K.Mk, e: K.Mk, vec: K.Mk): K.Mk =>
  K.primMk(K.OP_CAST_VEC, [a, n, m, e, vec]);
export const ifLeMk = (level: number, result: K.Mk, a: K.Mk, b: K.Mk, yes: K.Mk, no: K.Mk): K.Mk =>
  K.primMk(K.OP_IF_LE, [result, a, b, yes, no], level);
export const byContraMk = (a: K.Mk, b: K.Mk, k: K.Mk): K.Mk => K.primMk(K.OP_BY_CONTRA, [a, b, k]);
export const intEqMk = (a: K.Mk, b: K.Mk, p: K.Mk, q: K.Mk): K.Mk => K.primMk(K.OP_INT_EQ, [a, b, p, q]);
export const divFloorMk = (e: K.Mk, k: K.Mk): K.Mk => K.primMk(K.OP_DIV_FLOOR, [e, k]);
export const divFloorSpecMk = (e: K.Mk, k: K.Mk): K.Mk => K.primMk(K.OP_DIV_FLOOR_SPEC, [e, k]);
export const divTruncMk = (e: K.Mk, k: K.Mk): K.Mk => K.primMk(K.OP_DIV_TRUNC, [e, k]);
export const divTruncSpecNonnegMk = (e: K.Mk, k: K.Mk, h: K.Mk): K.Mk =>
  K.primMk(K.OP_DIV_TRUNC_SPEC_NONNEG, [e, k, h]);
export const divTruncSpecNegMk = (e: K.Mk, k: K.Mk, h: K.Mk): K.Mk =>
  K.primMk(K.OP_DIV_TRUNC_SPEC_NEG, [e, k, h]);
export const farkasMk = (hyps: readonly K.Mk[], coeffs: readonly bigint[]): K.Mk => K.farkasMk(hyps, coeffs);
export const lamMk = (name: string, domain: K.Mk, body: K.Mk): K.Mk => K.lamMk(name, domain, body);
export const piMk = (name: string, domain: K.Mk, body: K.Mk): K.Mk => K.piMk(name, domain, body);

/** `byContra a b (fun k => Farkas [k] [1])`, the proof of a literal `Le a b`. */
export const leProofMk = (a: bigint, b: bigint): K.Mk => () => K.LeProof(a, b);

/** The bounds proof `And (Le 0 i) (Lt i n)` for literals: a pair of Farkas proofs. */
export const boundsProof = (i: bigint, n: bigint): K.Term =>
  K.pair(
    K.And(K.Le(K.intLit(0n), K.intLit(i)), K.Lt(K.intLit(i), K.intLit(n))),
    K.LeProof(0n, i),
    K.LeProof(i + 1n, n),
  );

// ---------------------------------------------------------------------------
// Small runners
// ---------------------------------------------------------------------------

export const eval0 = (term: K.Term): K.Value => K.evalTerm(env, term, []);
export const infer = (term: K.Term): K.Result<K.Term> => K.inferType(env, term);
export const check = (term: K.Term, type: K.Term): K.Result<void> => K.checkType(env, term, type);
export const conv = (a: K.Term, b: K.Term): boolean => K.isConvertible(env, a, b);
export const norm = (term: K.Term): K.Term => {
  const out = K.normalize(env, term);
  if (!out.ok) throw new Error(K.formatKernelError(out.error));
  return out.value;
};
export const show = (term: K.Term): string => K.formatTerm(term);
export const showType = (term: K.Term): string => {
  const out = K.inferType(env, term);
  if (!out.ok) throw new Error(K.formatKernelError(out.error));
  return K.formatTerm(out.value);
};
