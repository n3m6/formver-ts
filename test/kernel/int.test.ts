/**
 * Milestone 3: linear integer values, the primitive proposition `Le`, the definitions
 * `Lt` and `InRange`, `ifLe`/`byContra`/`intEq`, and division by a constant.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { expectErr, expectOk } from "./helpers";
import {
  addMk,
  andMk,
  byContraMk,
  conv,
  divFloorMk,
  divFloorSpecMk,
  divTruncMk,
  divTruncSpecNegMk,
  divTruncSpecNonnegMk,
  env,
  eqMk,
  eval0,
  farkasMk,
  ifLeMk,
  inRangeMk,
  intEqMk,
  intMk,
  leMk,
  leProofMk,
  ltMk,
  mulConstMk,
  negMk,
  norm,
  subMk,
  show,
  showType,
  v,
} from "./helpers3";

const lit = K.intLit;

describe("linear values of type Int", () => {
  test("add, sub, neg and mulConst reduce to literals", () => {
    expect(show(norm(K.Add(lit(2), lit(3))))).toBe("5");
    expect(show(norm(K.Sub(lit(2), lit(3))))).toBe("-1");
    expect(show(norm(K.Neg(lit(3))))).toBe("-3");
    expect(show(norm(K.MulConst(lit(4), lit(-3))))).toBe("-12");
    expect(show(norm(K.MulConst(lit(0), K.primTerm(K.OP_FIX_WF, []))))).toBe("0");
  });

  test("n + 0, 0 + n and n are the same value", () => {
    const nPlusZero = K.mk(K.lamMk("n", intMk, addMk(v("n"), K.intLitMk(0n))));
    const zeroPlusN = K.mk(K.lamMk("n", intMk, addMk(K.intLitMk(0n), v("n"))));
    const plain = K.mk(K.lamMk("n", intMk, v("n")));
    expect(conv(nPlusZero, plain)).toBe(true);
    expect(conv(zeroPlusN, plain)).toBe(true);
    expect(conv(nPlusZero, zeroPlusN)).toBe(true);
  });

  test("n - n is 0 and 2 * x is x + x", () => {
    expect(conv(K.mk(K.lamMk("n", intMk, subMk(v("n"), v("n")))), K.mk(K.lamMk("n", intMk, K.intLitMk(0n))))).toBe(
      true,
    );
    expect(
      conv(
        K.mk(K.lamMk("x", intMk, mulConstMk(2n, v("x")))),
        K.mk(K.lamMk("x", intMk, addMk(v("x"), v("x")))),
      ),
    ).toBe(true);
  });

  test("2 * x is not x + 1, and n is not n + 1", () => {
    expect(
      conv(
        K.mk(K.lamMk("x", intMk, mulConstMk(2n, v("x")))),
        K.mk(K.lamMk("x", intMk, addMk(v("x"), K.intLitMk(1n)))),
      ),
    ).toBe(false);
    expect(
      conv(
        K.mk(K.lamMk("n", intMk, v("n"))),
        K.mk(K.lamMk("n", intMk, addMk(v("n"), K.intLitMk(1n)))),
      ),
    ).toBe(false);
  });

  test("distinct variables never share an atom key, at any depth", () => {
    const xy = K.mk(K.lamMk("x", intMk, K.lamMk("y", intMk, subMk(v("x"), v("y")))));
    const yx = K.mk(K.lamMk("x", intMk, K.lamMk("y", intMk, subMk(v("y"), v("x")))));
    const same = K.mk(K.lamMk("x", intMk, K.lamMk("y", intMk, subMk(v("x"), v("y")))));
    expect(conv(xy, yx)).toBe(false);
    expect(conv(xy, same)).toBe(true);
  });

  test("a non-literal multiplier stays stuck and is an atom", () => {
    const stuckTwo = K.mk(K.lamMk("n", intMk, mulConstMk(v("n"), K.intLitMk(2n))));
    const stuckOther = K.mk(K.lamMk("n", intMk, mulConstMk(v("n"), K.intLitMk(3n))));
    // The coefficient of the stuck op is not known, so all three are distinct atoms.
    expect(conv(stuckTwo, stuckTwo)).toBe(true);
    expect(conv(stuckTwo, stuckOther)).toBe(false);
    expect(showType(K.mk(K.lamMk("n", intMk, mulConstMk(v("n"), K.intLitMk(2n)))))).toBe("((n : Int()) -> Int())");
  });

  test("atom keys see through the linear normal form of an argument", () => {
    const direct = K.mk(K.lamMk("n", intMk, mulConstMk(v("n"), K.intLitMk(2n))));
    const computed = K.mk(K.lamMk("n", intMk, mulConstMk(v("n"), addMk(K.intLitMk(1n), K.intLitMk(1n)))));
    expect(conv(direct, computed)).toBe(true);
  });
});

describe("Le, Lt and InRange", () => {
  test("Le a b and Le c d are convertible when b - a and d - c agree", () => {
    expect(conv(K.Le(lit(1), lit(2)), K.Le(lit(2), lit(3)))).toBe(true);
    expect(conv(K.Le(lit(2), lit(1)), K.Le(lit(2), lit(2)))).toBe(false);
    expect(
      conv(
        K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), v("b"))))),
        K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(subMk(v("a"), K.intLitMk(1n)), subMk(v("b"), K.intLitMk(1n)))))),
      ),
    ).toBe(true);
  });

  test("Le a b is never Le a (b + 1), nor Le (a - 1) b", () => {
    const base = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), v("b")))));
    const shiftedRight = K.mk(
      K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), addMk(v("b"), K.intLitMk(1n))))),
    );
    const shiftedLeft = K.mk(
      K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(subMk(v("a"), K.intLitMk(1n)), v("b")))),
    );
    expect(conv(base, shiftedRight)).toBe(false);
    expect(conv(base, shiftedLeft)).toBe(false);
  });

  test("Lt a b is the definition Le (a + 1) b, and not Le a (b + 1)", () => {
    const lt = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, ltMk(v("a"), v("b")))));
    const unfolded = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(addMk(v("a"), K.intLitMk(1n)), v("b")))));
    const wrong = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), addMk(v("b"), K.intLitMk(1n))))));
    expect(conv(lt, unfolded)).toBe(true);
    expect(conv(lt, wrong)).toBe(false);
    expect(showType(K.Lt(lit(1), lit(2)))).toBe("Type 0");
  });

  test("InRange is the definition And (Le (-(2^53-1)) x) (Le x (2^53-1))", () => {
    const definition = K.mk(
      K.lamMk("x", intMk, inRangeMk(v("x"))),
    );
    const unfolded = K.mk(
      K.lamMk(
        "x",
        intMk,
        andMk(leMk(negMk(K.intLitMk(K.SAFE_MAX)), v("x")), leMk(v("x"), K.intLitMk(K.SAFE_MAX))),
      ),
    );
    expect(conv(definition, unfolded)).toBe(true);
    expect(showType(K.InRange(lit(5)))).toBe("Type 0");
    // InRange is not a `Le`, so it can never be a Farkas hypothesis.
    expect(expectErr(K.checkFarkas({ hypTypes: [eval0(K.InRange(lit(5)))], coeffs: [1n] })).reason).toBe(
      "farkas-not-a-le-hypothesis",
    );
  });

  test("the prelude still has zero axioms", () => {
    expect(K.axiomsUsed(env)).toEqual([]);
    for (const name of [K.LT_NAME, K.IN_RANGE_NAME]) {
      expect(K.lookupDecl(env, name)?.kind).toBe("def");
    }
  });
});

describe("ifLe", () => {
  const yes = K.lam("_", K.Le(lit(1), lit(2)), lit(10));
  const no = K.lam("_", K.Lt(lit(2), lit(1)), lit(20));

  test("reduces to the yes branch when a <= b", () => {
    const term = K.IfLe(0, K.Int, lit(1), lit(2), yes, K.lam("_", K.Lt(lit(2), lit(1)), lit(20)));
    expect(show(norm(term))).toBe("10");
    expect(K.inferType(env, term).ok).toBe(true);
  });

  test("reduces to the no branch when a > b", () => {
    const term = K.IfLe(0, K.Int, lit(3), lit(2), K.lam("_", K.Le(lit(3), lit(2)), lit(10)), K.lam("_", K.Lt(lit(2), lit(3)), lit(20)));
    expect(show(norm(term))).toBe("20");
    expect(K.inferType(env, term).ok).toBe(true);
  });

  test("with non-literal bounds it is stuck, and its type is the motive", () => {
    const term = K.mk(
      K.lamMk(
        "a",
        intMk,
        K.lamMk(
          "b",
          intMk,
          ifLeMk(
            0,
            intMk,
            v("a"),
            v("b"),
            K.lamMk("_", leMk(v("a"), v("b")), K.intLitMk(1n)),
            K.lamMk("_", ltMk(v("b"), v("a")), K.intLitMk(2n)),
          ),
        ),
      ),
    );
    expect(showType(term)).toBe("((a : Int()) -> ((b : Int()) -> Int()))");
    // The two branches are relevant: a stuck ifLe with a different branch is a different
    // value, because the result is a value of the motive, not a proof.
    const other = K.mk(
      K.lamMk(
        "a",
        intMk,
        K.lamMk(
          "b",
          intMk,
          ifLeMk(
            0,
            intMk,
            v("a"),
            v("b"),
            K.lamMk("_", leMk(v("a"), v("b")), K.intLitMk(3n)),
            K.lamMk("_", ltMk(v("b"), v("a")), K.intLitMk(2n)),
          ),
        ),
      ),
    );
    expect(conv(term, other)).toBe(false);
  });

  test("normalizing a literal ifLe quotes the synthesized branch proof", () => {
    const term = K.IfLe(0, K.Int, lit(1), lit(2), yes, no);
    const normal = K.normalize(env, term);
    expect(expectOk(normal)).toEqual(K.intLit(10));
  });

  test("the branch proof `ifLe` synthesizes is a real kernel proof", () => {
    // `ifLe Int 1 2 (fun h => h) (fun _ => LeProof 1 2) : Le 1 2` reduces to the proof
    // that `ifLe` built from `byContra` and a one-hypothesis Farkas certificate, and that
    // normal form still typechecks (it is quoted and re-checked here).
    const term = K.IfLe(
      0,
      K.Le(lit(1), lit(2)),
      lit(1),
      lit(2),
      K.lam("h", K.Le(lit(1), lit(2)), K.varTerm(0)),
      K.lam("_", K.Lt(lit(2), lit(1)), K.LeProof(1n, 2n)),
    );
    expect(K.checkType(env, term, K.Le(lit(1), lit(2))).ok).toBe(true);
    const normal = norm(term);
    expect(K.checkType(env, normal, K.Le(lit(1), lit(2))).ok).toBe(true);
    expect(show(normal)).toContain("byContra");
    expect(show(normal)).toContain("farkas");
    // The proof is irreducibly a proof: it is not convertible with a proof built from a
    // different refutation, but conversion accepts it where `Le 1 2` is expected.
    expect(conv(normal, K.LeProof(1n, 2n))).toBe(true);
  });

  test("a level-parametric motive works at level 1", () => {
    const term = K.IfLe(
      1,
      K.sort(0),
      lit(1),
      lit(2),
      K.lam("_", K.Le(lit(1), lit(2)), K.Unit),
      K.lam("_", K.Lt(lit(2), lit(1)), K.Unit),
    );
    expect(show(norm(term))).toBe("Unit()");
  });
});

describe("byContra and intEq", () => {
  test("byContra proves a literal Le with a Farkas refutation", () => {
    const proof = K.LeProof(3, 7);
    expect(K.checkType(env, proof, K.Le(lit(3), lit(7))).ok).toBe(true);
    expect(showType(proof)).toBe("Le(3, 7)");
  });

  test("byContra keeps its second argument irrelevant", () => {
    // Two refutations of `Lt 7 3` with different multipliers: both prove `Le 3 7`, and
    // the refutation argument of `byContra` is irrelevant, so they are convertible.
    const refute = (coeff: bigint): K.Mk =>
      K.lamMk("k", ltMk(K.intLitMk(7n), K.intLitMk(3n)), farkasMk([v("k")], [coeff]));
    const left = K.mk(byContraMk(K.intLitMk(3n), K.intLitMk(7n), refute(1n)));
    const right = K.mk(byContraMk(K.intLitMk(3n), K.intLitMk(7n), refute(2n)));
    expect(K.checkType(env, left, K.Le(lit(3), lit(7))).ok).toBe(true);
    expect(K.checkType(env, right, K.Le(lit(3), lit(7))).ok).toBe(true);
    expect(conv(left, right)).toBe(true);
    expect(conv(left, K.LeProof(3, 7))).toBe(true);
  });

  test("intEq turns the two directions into an Eq Int", () => {
    const term = K.mk(
      K.lamMk(
        "n0",
        intMk,
        K.lamMk(
          "n1",
          intMk,
          K.lamMk(
            "p",
            leMk(v("n0"), v("n1")),
            K.lamMk("q", leMk(v("n1"), v("n0")), intEqMk(v("n0"), v("n1"), v("p"), v("q"))),
          ),
        ),
      ),
    );
    const type = K.mk(
      K.piMk(
        "n0",
        intMk,
        K.piMk(
          "n1",
          intMk,
          K.piMk("p", leMk(v("n0"), v("n1")), K.piMk("q", leMk(v("n1"), v("n0")), eqMk(intMk, v("n0"), v("n1")))),
        ),
      ),
    );
    expect(K.checkType(env, term, type).ok).toBe(true);
    // The two directions also prove `Eq Int (n0 + 0) n1`, since the arguments of `Eq`
    // compare by linear normal form.
    const shifted = K.mk(
      K.piMk(
        "n0",
        intMk,
        K.piMk(
          "n1",
          intMk,
          K.piMk("p", leMk(v("n0"), v("n1")), K.piMk("q", leMk(v("n1"), v("n0")), eqMk(intMk, addMk(v("n0"), K.intLitMk(0n)), v("n1")))),
        ),
      ),
    );
    expect(K.checkType(env, term, shifted).ok).toBe(true);
  });

  test("intEq is not convertible with refl, but both inhabit the same Eq type", () => {
    const eqType = K.Eq(K.Int, lit(4), lit(4));
    const viaIntEq = K.IntEq(lit(4), lit(4), K.LeProof(4, 4), K.LeProof(4, 4));
    expect(K.checkType(env, viaIntEq, eqType).ok).toBe(true);
    expect(K.checkType(env, K.Refl(K.Int, lit(4)), eqType).ok).toBe(true);
    expect(conv(viaIntEq, K.Refl(K.Int, lit(4)))).toBe(false);
  });
});

describe("division by a constant", () => {
  test("divFloor and divTrunc reduce on literals", () => {
    expect(show(norm(K.DivFloor(lit(7), lit(2))))).toBe("3");
    expect(show(norm(K.DivFloor(lit(-7), lit(2))))).toBe("-4");
    expect(show(norm(K.DivTrunc(lit(7), lit(2))))).toBe("3");
    expect(show(norm(K.DivTrunc(lit(-7), lit(2))))).toBe("-3");
    expect(show(norm(K.DivFloor(lit(6), lit(3))))).toBe("2");
    expect(show(norm(K.DivTrunc(lit(-8), lit(4))))).toBe("-2");
  });

  test("a non-literal dividend leaves division stuck", () => {
    const term = K.mk(K.lamMk("e", intMk, divFloorMk(v("e"), K.intLitMk(2n))));
    expect(showType(term)).toBe("((e : Int()) -> Int())");
    expect(show(norm(K.mk(K.appMk(K.lamMk("e", intMk, divFloorMk(v("e"), K.intLitMk(2n))), K.intLitMk(0n)))))).toBe("0");
  });

  test("the divisor must be a positive integer literal", () => {
    const variable = K.mk(K.lamMk("k", intMk, K.primMk(K.OP_DIV_FLOOR, [K.intLitMk(3n), v("k")])));
    expect(expectErr(K.inferType(env, variable)).reason).toBe("prim-not-literal");
    expect(expectErr(K.inferType(env, K.DivFloor(lit(3), lit(0)))).reason).toBe("prim-not-literal");
    expect(expectErr(K.inferType(env, K.DivFloor(lit(3), lit(-2)))).reason).toBe("prim-not-literal");
    // A divisor that is a *computation*, not a literal, is rejected too.
    expect(expectErr(K.inferType(env, K.DivFloor(lit(3), K.Add(lit(1), lit(1))))).reason).toBe(
      "prim-not-literal",
    );
    expect(expectErr(K.inferType(env, K.DivTrunc(lit(3), lit(0)))).reason).toBe("prim-not-literal");
    expect(expectErr(K.inferType(env, K.DivFloorSpec(lit(3), lit(0)))).reason).toBe("prim-not-literal");
    expect(
      expectErr(
        K.inferType(env, K.DivTruncSpecNonneg(lit(3), lit(0), K.LeProof(0n, 3n))),
      ).reason,
    ).toBe("prim-not-literal");
    expect(
      expectErr(K.inferType(env, K.DivTruncSpecNeg(lit(-3), lit(0), K.LeProof(0n, 0n)))).reason,
    ).toBe("prim-not-literal");
  });

  test("divFloorSpec has the specified type for a variable dividend", () => {
    const expected = K.mk(
      K.piMk(
        "e",
        intMk,
        andMk(
          leMk(mulConstMk(2n, divFloorMk(v("e"), K.intLitMk(2n))), v("e")),
          leMk(v("e"), addMk(mulConstMk(2n, divFloorMk(v("e"), K.intLitMk(2n))), K.intLitMk(1n))),
        ),
      ),
    );
    const term = K.mk(K.lamMk("e", intMk, divFloorSpecMk(v("e"), K.intLitMk(2n))));
    expect(K.checkType(env, term, expected).ok).toBe(true);
  });

  test("the divTrunc lemmas have the specified types", () => {
    const nonneg = K.mk(
      K.piMk(
        "e",
        intMk,
        K.piMk(
          "h",
          leMk(K.intLitMk(0n), v("e")),
          andMk(
            leMk(mulConstMk(2n, divTruncMk(v("e"), K.intLitMk(2n))), v("e")),
            leMk(v("e"), addMk(mulConstMk(2n, divTruncMk(v("e"), K.intLitMk(2n))), K.intLitMk(1n))),
          ),
        ),
      ),
    );
    expect(
      K.checkType(env, K.mk(K.lamMk("e", intMk, K.lamMk("h", leMk(K.intLitMk(0n), v("e")), divTruncSpecNonnegMk(v("e"), K.intLitMk(2n), v("h"))))), nonneg).ok,
    ).toBe(true);

    const negative = K.mk(
      K.piMk(
        "e",
        intMk,
        K.piMk(
          "h",
          ltMk(v("e"), K.intLitMk(0n)),
          andMk(
            leMk(addMk(subMk(mulConstMk(2n, divTruncMk(v("e"), K.intLitMk(2n))), K.intLitMk(2n)), K.intLitMk(1n)), v("e")),
            leMk(v("e"), mulConstMk(2n, divTruncMk(v("e"), K.intLitMk(2n)))),
          ),
        ),
      ),
    );
    expect(
      K.checkType(env, K.mk(K.lamMk("e", intMk, K.lamMk("h", ltMk(v("e"), K.intLitMk(0n)), divTruncSpecNegMk(v("e"), K.intLitMk(2n), v("h"))))), negative).ok,
    ).toBe(true);
  });

  test("a spec lemma's claim is convertible with its literal bounds", () => {
    // `2 * divFloor 7 2` is 6 and `2 * divFloor 7 2 + 2 - 1` is 7, so the lemma has the
    // type `And (Le 6 7) (Le 7 7)`; checking it against that type exercises the reduction
    // of the lemma's statement.
    expect(
      K.checkType(env, K.DivFloorSpec(lit(7), lit(2)), K.And(K.Le(lit(6), lit(7)), K.Le(lit(7), lit(7)))).ok,
    ).toBe(true);
    expect(
      K.checkType(env, K.DivTrunc(lit(7), lit(2)), K.Int).ok,
    ).toBe(true);
  });
});

describe("canonical atom keys", () => {
  const key = (value: K.Value): string => K.keyOfValue(value, K.irrelevantOf);

  test("free variables are named by level and bound ones by traversal position", () => {
    // λy. λx. x and λy. λx. y differ only in *which* variable the innermost body uses.
    const inner = K.evalTerm(env, K.lam("y", K.Int, K.lam("x", K.Int, K.varTerm(0))), []);
    const outer = K.evalTerm(env, K.lam("y", K.Int, K.lam("x", K.Int, K.varTerm(1))), []);
    expect(key(inner)).not.toBe(key(outer));
    // Renaming the binders changes nothing.
    const renamed = K.evalTerm(env, K.lam("p", K.Int, K.lam("q", K.Int, K.varTerm(0))), []);
    expect(key(renamed)).toBe(key(inner));
    // Nor does the size of the environment the closure happened to be created under.
    const underABinder = K.evalTerm(env, K.lam("y", K.Int, K.lam("x", K.Int, K.varTerm(0))), [K.vvar(0)]);
    expect(key(underABinder)).toBe(key(inner));
  });

  test("a closure's free variables keep their own names", () => {
    // Under `fun y => fun x => y`: the body's free variable is the outer binder.
    const usesOuter = K.evalTerm(env, K.lam("y", K.Int, K.lam("x", K.Int, K.varTerm(1))), []);
    const usesFreeLevel0 = K.evalTerm(env, K.lam("x", K.Int, K.varTerm(1)), [K.vvar(0)]);
    expect(key(usesOuter)).not.toBe(key(usesFreeLevel0));
  });

  test("proof arguments are erased from keys, and lengths are normalized", () => {
    const vector = K.vvar(0);
    const boundsType = K.And(K.Le(K.intLit(0), K.intLit(1)), K.Lt(K.intLit(1), K.intLit(3)));
    const proofA = K.evalTerm(env, K.LeProof(0n, 1n), []);
    const proofB = K.evalTerm(env, K.pair(boundsType, K.LeProof(0n, 1n), K.LeProof(2n, 3n)), []);
    /** `get Int n vector i proof` as a value, with `vector` at level 0 and the proof at 1. */
    const getAt = (n: K.Term, i: K.Term, proof: K.Value): K.Value =>
      K.evalTerm(env, K.Get(K.Int, n, K.varTerm(1), i, K.varTerm(0)), [vector, proof]);
    expect(key(getAt(K.intLit(3), K.intLit(1), proofA))).toBe(key(getAt(K.intLit(3), K.intLit(1), proofB)));
    // `1 + 2` is the same length as `3`.
    expect(key(getAt(K.Add(K.intLit(1), K.intLit(2)), K.intLit(1), proofA))).toBe(
      key(getAt(K.intLit(3), K.intLit(1), proofA)),
    );
    // A different index is a different atom.
    expect(key(getAt(K.intLit(3), K.intLit(2), proofA))).not.toBe(key(getAt(K.intLit(3), K.intLit(1), proofA)));
  });
});
