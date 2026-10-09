/**
 * Bidirectional checking: universes, dependent functions and pairs, and the rejections
 * that matter for soundness (no `Type : Type`, no Girard-style self-application, no
 * ill-typed applications, lambdas or pairs).
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { depSigma, endoId, expectErr, expectOk, expectReason, identity, idType, natType } from "./helpers";

const env = K.emptyEnv();
const unitToUnit: K.Term = K.pi("_", K.Unit, K.Unit);

describe("universes", () => {
  test("Type l : Type (l+1)", () => {
    expect(K.formatTerm(expectOk(K.inferType(env, K.sort(0))))).toBe("Type 1");
    expect(K.formatTerm(expectOk(K.inferType(env, K.sort(3))))).toBe("Type 4");
    expect(K.checkType(env, K.sort(0), K.sort(1)).ok).toBe(true);
    expect(K.checkType(env, K.sort(5), K.sort(6)).ok).toBe(true);
  });

  test("Type 0 : Type 0 is rejected", () => {
    expectReason(K.checkType(env, K.sort(0), K.sort(0)), "type-mismatch");
  });

  test("Type l : Type l is rejected for every l", () => {
    for (const level of [0, 1, 2, 7]) {
      expectReason(K.checkType(env, K.sort(level), K.sort(level)), "type-mismatch");
    }
  });

  test("Pi and Sigma take the maximum of the domain and codomain levels", () => {
    // (A : Type 0) -> Type 0 : the domain lives in Type 1, the codomain in Type 1.
    expect(K.formatTerm(expectOk(K.inferType(env, K.pi("A", K.sort(0), K.sort(0)))))).toBe("Type 1");
    // (A : Type 0) -> Type 3 : max(1, 4).
    expect(K.formatTerm(expectOk(K.inferType(env, K.pi("A", K.sort(0), K.sort(3)))))).toBe("Type 4");
    // (A : Type 2) -> Type 0 : max(3, 1).
    expect(K.formatTerm(expectOk(K.inferType(env, K.pi("A", K.sort(2), K.sort(0)))))).toBe("Type 3");
    expect(K.formatTerm(expectOk(K.inferType(env, K.sigma("A", K.sort(1), K.sort(2)))))).toBe("Type 3");
    expect(K.formatTerm(expectOk(K.inferType(env, natType)))).toBe("Type 1");
  });

  test("a Pi whose domain is not a type is rejected", () => {
    expectReason(K.inferType(env, K.pi("x", K.tt, K.tt)), "not-a-type");
  });

  test("a Pi whose codomain is not a type is rejected", () => {
    expectReason(K.inferType(env, K.pi("x", K.Unit, K.varTerm(0))), "not-a-type");
  });

  test("a universe level cannot be used as a value", () => {
    expectReason(K.inferType(env, K.app(K.sort(0), K.tt)), "not-a-function");
  });
});

describe("Girard-style self-application", () => {
  test("fun (x : Type 0) => x x is rejected", () => {
    const term = K.lam("x", K.sort(0), K.app(K.varTerm(0), K.varTerm(0)));
    expectReason(K.inferType(env, term), "not-a-function");
    expect(K.checkType(env, term, K.pi("x", K.sort(0), K.sort(1))).ok).toBe(false);
  });

  test("the classic self-application of a self-application is rejected", () => {
    const delta = K.lam("x", K.sort(0), K.app(K.varTerm(0), K.varTerm(0)));
    expectReason(K.inferType(env, K.app(delta, delta)), "not-a-function");
  });

  test("applying a type to an argument is rejected", () => {
    expectReason(K.inferType(env, K.app(K.Unit, K.tt)), "not-a-function");
  });

  test("no term of type (A : Type 0) -> A is constructible from Type alone", () => {
    // The would-be Girard term `fun A => A A`-style applications cannot typecheck.
    const bad = K.lam("A", K.sort(0), K.app(K.varTerm(0), K.varTerm(0)));
    expect(K.checkType(env, bad, K.pi("A", K.sort(0), K.varTerm(0))).ok).toBe(false);
  });
});

describe("ill-typed applications", () => {
  test("applying a non-function is rejected", () => {
    expectReason(K.inferType(env, K.app(K.tt, K.tt)), "not-a-function");
  });

  test("applying a function to an argument of the wrong type is rejected", () => {
    expectReason(K.checkType(env, K.app(identity, K.tt), K.Empty), "type-mismatch");
    expectReason(K.inferType(env, K.app(identity, K.tt)), "type-mismatch");
  });

  test("too many arguments are rejected", () => {
    // ((fun x => x) Unit tt) is `tt : Unit`, which is not a function.
    expectReason(K.inferType(env, K.app(K.app(K.app(identity, K.Unit), K.tt), K.tt)), "not-a-function");
    const id = K.lam("x", K.Unit, K.varTerm(0));
    expectReason(K.inferType(env, K.app(K.app(id, K.tt), K.tt)), "not-a-function");
  });

  test("too few arguments leave a function type", () => {
    expect(K.formatTerm(expectOk(K.inferType(env, K.app(identity, K.Unit))))).toBe("((x : Unit()) -> Unit())");
  });

  test("a function used where a type is expected is rejected", () => {
    expectReason(K.inferType(env, K.pi("x", endoId, K.Unit)), "not-a-type");
  });
});

describe("ill-typed lambdas", () => {
  test("wrong domain annotation", () => {
    const term = K.lam("x", K.Empty, K.varTerm(0));
    const expected = K.pi("_", K.Unit, K.Unit);
    expectReason(K.checkType(env, term, expected), "type-mismatch");
  });

  test("wrong codomain", () => {
    const term = K.lam("x", K.Unit, K.tt);
    const expected = K.pi("_", K.Unit, K.Empty);
    expectReason(K.checkType(env, term, expected), "type-mismatch");
  });

  test("wrong arity", () => {
    // (fun A x => x) : (A : Type 0) -> A -> A, checked against (A : Type 0) -> A -> A -> A
    const term = K.lam("A", K.sort(0), K.lam("x", K.varTerm(0), K.varTerm(0)));
    const expected = K.mk(
      K.piMk(
        "A",
        K.sortMk(0),
        K.piMk("x", K.varMk("A"), K.piMk("y", K.varMk("A"), K.varMk("A"))),
      ),
    );
    expectReason(K.checkType(env, term, expected), "type-mismatch");
  });

  test("a lambda checked against a non-function type is rejected", () => {
    expectReason(K.checkType(env, endoId, K.Unit), "type-mismatch");
  });

  test("a lambda body may not use an out-of-scope variable", () => {
    expectReason(K.inferType(env, K.lam("x", K.Unit, K.varTerm(1))), "unbound-variable");
  });
});

describe("ill-typed pairs", () => {
  test("a pair whose annotation is not a Sigma type is rejected", () => {
    expectReason(K.inferType(env, K.pair(K.Unit, K.tt, K.tt)), "not-a-sigma");
  });

  test("a pair checked against a different Sigma type is rejected", () => {
    const term = K.pair(depSigma, K.Unit, endoId);
    const wrong = K.sigma("A", K.sort(0), K.pi("_", K.varTerm(0), K.Empty));
    expectReason(K.checkType(env, term, wrong), "type-mismatch");
  });

  test("a pair with a wrong second component is rejected", () => {
    // <Unit, tt> : Sigma (A : Type 0). A -> A  --  tt is not a function.
    expectReason(K.inferType(env, K.pair(depSigma, K.Unit, K.tt)), "type-mismatch");
  });

  test("a pair checked against a function type is rejected", () => {
    expectReason(K.checkType(env, K.pair(K.And(K.Unit, K.Unit), K.tt, K.tt), unitToUnit), "type-mismatch");
  });

  test("fst/snd of a non-pair is rejected", () => {
    expectReason(K.inferType(env, K.fst(K.tt)), "not-a-sigma");
    expectReason(K.inferType(env, K.snd(K.tt)), "not-a-sigma");
    expectReason(K.inferType(env, K.snd(K.Unit)), "not-a-sigma");
  });
});

describe("primitive ops", () => {
  test("unknown ops are rejected, not ignored", () => {
    expectReason(K.inferType(env, K.primTerm("NoSuchOp", [])), "unknown-prim");
    expectReason(K.inferType(env, K.primTerm("noSuchOpEither", [K.tt])), "unknown-prim");
    // `get` is a milestone-3 built-in, so its wrong *arity* is reported as such.
    expectReason(K.inferType(env, K.primTerm(K.OP_GET, [K.tt])), "prim-arity");
  });

  test("wrong arity is rejected", () => {
    expectReason(K.inferType(env, K.primTerm(K.OP_SUM, [K.Unit])), "prim-arity");
    expectReason(K.inferType(env, K.primTerm(K.OP_SUM, [K.Unit, K.Unit, K.Unit])), "prim-arity");
    expectReason(K.inferType(env, K.primTerm(K.OP_EMPTY, [K.Unit])), "prim-arity");
  });

  test("primitive arguments are checked against the telescope", () => {
    expect(K.checkType(env, K.tt, K.Unit).ok).toBe(true);
    expectReason(K.inferType(env, K.primTerm(K.OP_REFL, [K.Empty, K.tt])), "type-mismatch");
    expectReason(K.inferType(env, K.Absurd(0, K.Unit, K.tt)), "type-mismatch");
  });

  test("primitive types are the specified ones", () => {
    expect(K.formatTerm(expectOk(K.inferType(env, K.Empty)))).toBe("Type 0");
    expect(K.formatTerm(expectOk(K.inferType(env, K.tt)))).toBe("Unit()");
    expect(K.formatTerm(expectOk(K.inferType(env, K.Int)))).toBe("Type 0");
    expect(K.formatTerm(expectOk(K.inferType(env, K.intLit(5))))).toBe("Int()");
    expect(K.formatTerm(expectOk(K.inferType(env, K.Le(K.intLit(1), K.intLit(2)))))).toBe("Type 0");
    expect(K.formatTerm(expectOk(K.inferType(env, K.Sum(K.Unit, K.Unit))))).toBe("Type 0");
    expect(K.formatTerm(expectOk(K.inferType(env, K.Eq(K.Unit, K.tt, K.tt))))).toBe("Type 0");
    expect(K.formatTerm(expectOk(K.inferType(env, K.Refl(K.Unit, K.tt))))).toBe("Eq(Unit(), tt(), tt())");
  });

  test("Sum elimination at a higher universe level", () => {
    // case into Type 1 is allowed because the eliminator's motive is level-parametric.
    const motive = K.lam("s", K.Sum(K.Unit, K.Unit), K.sort(0));
    const onLeft = K.lam("a", K.Unit, K.Unit);
    const onRight = K.lam("b", K.Unit, K.Unit);
    const term = K.SumCase(1, K.Unit, K.Unit, motive, onLeft, onRight, K.Inl(K.Unit, K.Unit, K.tt));
    expect(K.formatTerm(expectOk(K.inferType(env, term)))).toBe("Type 0");
  });

  test("absurd's motive is level-parametric", () => {
    // fun (h : Le 2 1) => absurd {l=1} (Type 0) (Farkas [h] [1]) : Le 2 1 -> Type 0
    const le21 = K.Le(K.intLit(2), K.intLit(1));
    const term = K.lam("h", le21, K.Absurd(1, K.sort(0), K.Farkas([K.varTerm(0)], [1n])));
    expect(K.formatTerm(expectOk(K.inferType(env, term)))).toBe(`((h : ${K.formatTerm(le21)}) -> Type 0)`);
    // The same term at level 0 gives the proposition `Empty`, which is not a type of types.
    const atZero = K.lam("h", le21, K.Absurd(0, K.Empty, K.Farkas([K.varTerm(0)], [1n])));
    expect(K.formatTerm(expectOk(K.inferType(env, atZero)))).toBe(`((h : ${K.formatTerm(le21)}) -> Empty())`);
  });
});

describe("Farkas typing", () => {
  const le21 = K.Le(K.intLit(2), K.intLit(1));
  const le22 = K.Le(K.intLit(2), K.intLit(2));

  test("a valid literal certificate has type Empty", () => {
    const term = K.lam("h", le21, K.Farkas([K.varTerm(0)], [1n]));
    expect(K.formatTerm(expectOk(K.inferType(env, term)))).toBe(`((h : ${K.formatTerm(le21)}) -> Empty())`);
    expect(K.checkType(env, term, K.pi("_", le21, K.Empty)).ok).toBe(true);
  });

  test("Farkas itself infers to Empty inside a context with a contradictory hypothesis", () => {
    const body = K.Farkas([K.varTerm(0)], [1n]);
    const term = K.lam("h", le21, body);
    expect(K.checkType(env, term, K.pi("_", le21, K.Empty)).ok).toBe(true);
  });

  test("a non-contradictory certificate is rejected", () => {
    const term = K.lam("h", le22, K.Farkas([K.varTerm(0)], [1n]));
    expectReason(K.checkType(env, term, K.pi("_", le22, K.Empty)), "farkas-invalid");
  });

  test("a negative multiplier is rejected", () => {
    const term = K.lam("h", le21, K.Farkas([K.varTerm(0)], [-1n]));
    expectReason(K.checkType(env, term, K.pi("_", le21, K.Empty)), "farkas-negative-coefficient");
  });

  test("a hypothesis whose type is not Le is rejected", () => {
    const term = K.lam("h", K.Unit, K.Farkas([K.varTerm(0)], [1n]));
    expectReason(K.checkType(env, term, K.pi("_", K.Unit, K.Empty)), "farkas-not-a-le-hypothesis");
    const eqHyp = K.lam("h", K.Eq(K.Unit, K.tt, K.tt), K.Farkas([K.varTerm(0)], [1n]));
    expectReason(K.checkType(env, eqHyp, K.pi("_", K.Eq(K.Unit, K.tt, K.tt), K.Empty)), "farkas-not-a-le-hypothesis");
  });

  test("a coefficient count mismatch is rejected", () => {
    const term = K.lam("h", le21, K.Farkas([K.varTerm(0)], [1n, 1n]));
    expectReason(K.checkType(env, term, K.pi("_", le21, K.Empty)), "farkas-shape");
  });

  test("an empty certificate proves nothing", () => {
    expectReason(K.inferType(env, K.Farkas([], [])), "farkas-invalid");
  });

  test("certificates over atoms are checked against the atom's linear row", () => {
    // `h : Le x 0` is the row `x <= 0`, which no non-zero multiplier can cancel: the
    // certificate is rejected, but as an arithmetic failure, not as "unsupported".
    const hypType = K.Le(K.varTerm(0), K.intLit(0));
    const bogus = K.lam("x", K.Int, K.lam("h", hypType, K.Farkas([K.varTerm(0)], [1n])));
    expectReason(K.checkType(env, bogus, K.pi("x", K.Int, K.pi("_", hypType, K.Empty))), "farkas-invalid");
    // `h : Le x x` is the row `0 <= 0`: still no contradiction to be had.
    const reflexive = K.Le(K.varTerm(0), K.varTerm(0));
    const trivial = K.lam("x", K.Int, K.lam("h", reflexive, K.Farkas([K.varTerm(0)], [1n])));
    expectReason(K.checkType(env, trivial, K.pi("x", K.Int, K.pi("_", reflexive, K.Empty))), "farkas-invalid");
    // `Le x 0` and `Le 0 x` cannot both hold at once: now the certificate is accepted.
    const reverse = K.Le(K.intLit(0), K.varTerm(0));
    const contradiction = K.lam(
      "x",
      K.Int,
      K.lam("h1", hypType, K.lam("h2", reverse, K.Farkas([K.varTerm(1), K.varTerm(0)], [1n, 1n]))),
    );
    expect(
      K.checkType(env, contradiction, K.pi("x", K.Int, K.pi("_", hypType, K.pi("_", reverse, K.Empty)))).ok,
    ).toBe(false);
  });

  test("a hypothesis that is not a proof is rejected by ordinary typing", () => {
    // The proposition `Le 2 1` itself (not a proof of it) is a type, not an inhabitant.
    const term = K.lam("h", K.Unit, K.Farkas([K.Le(K.intLit(2), K.intLit(1))], [1n]));
    expectErr(K.checkType(env, term, K.pi("_", K.Unit, K.Empty)));
  });

  test("the certificate term is typeable at Empty but cannot be used to build a value of Empty", () => {
    // `Farkas` only inhabits Empty, so it can never be confused with a data value.
    expect(K.checkType(env, K.tt, K.Empty).ok).toBe(false);
    expect(K.checkType(env, K.intLit(0), K.Empty).ok).toBe(false);
  });
});

describe("checkType validates the type annotation", () => {
  test("a non-type annotation is rejected", () => {
    expectReason(K.checkType(env, K.tt, K.tt), "not-a-type");
    expectReason(K.checkType(env, K.tt, K.lam("x", K.Unit, K.varTerm(0))), "not-a-type");
  });

  test("an ill-formed annotation is rejected", () => {
    expectReason(K.checkType(env, K.tt, K.constTerm("missing")), "unbound-constant");
    expectReason(K.checkType(env, K.tt, K.varTerm(3)), "unbound-variable");
  });

  test("checking against a convertible type succeeds", () => {
    const andUU = K.And(K.Unit, K.Unit);
    const sigmaForm = K.sigma("_", K.Unit, K.Unit);
    expect(K.checkType(env, K.pair(andUU, K.tt, K.tt), sigmaForm).ok).toBe(true);
    // ... and `tt` is not a pair, so this must fail.
    expect(K.checkType(env, K.tt, K.And(K.Unit, K.Unit)).ok).toBe(false);
  });

  test("idType and identity round-trip through infer/check", () => {
    const inferred = expectOk(K.inferType(env, identity));
    expect(K.checkType(env, identity, inferred).ok).toBe(true);
    expect(K.formatTerm(inferred)).toBe(K.formatTerm(idType));
  });
});
