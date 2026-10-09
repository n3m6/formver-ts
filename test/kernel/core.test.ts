/**
 * Kernel core (milestone 2 acceptance): identity, constant and composition functions,
 * Church numerals, dependent pairs with eta, `J` transport, and term utilities.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import {
  church,
  compose,
  composeType,
  constFn,
  constType,
  depPair,
  depSigma,
  endoId,
  expectErr,
  expectOk,
  expectReason,
  identity,
  idType,
  natType,
  plus,
  plusType,
  suc,
  sucType,
  transport,
  transportType,
} from "./helpers";

const env = K.emptyEnv();

const infer = (term: K.Term): K.Term => expectOk(K.inferType(env, term));
const check = (term: K.Term, type: K.Term): void => {
  const result = K.checkType(env, term, type);
  if (!result.ok) throw new Error(K.formatKernelError(result.error));
};
const normal = (term: K.Term): K.Term => expectOk(K.normalize(env, term));

describe("core typing", () => {
  test("identity typechecks and infers its type", () => {
    check(identity, idType);
    expect(K.formatTerm(infer(identity))).toBe(K.formatTerm(idType));
  });

  test("constant function typechecks", () => {
    check(constFn, constType);
  });

  test("composition typechecks", () => {
    check(compose, composeType);
  });

  test("applying identity to tt is convertible with tt", () => {
    const applied = K.app(K.app(identity, K.Unit), K.tt);
    expect(K.isConvertible(env, applied, K.tt)).toBe(true);
    check(applied, K.Unit);
  });

  test("type mismatch is reported with a structured reason", () => {
    expectReason(K.checkType(env, K.tt, K.Empty), "type-mismatch");
  });
});

describe("Church numerals", () => {
  test("zero, one, two and three all check against Nat", () => {
    for (const n of [0, 1, 2, 3, 7]) check(church(n), natType);
  });

  test("Nat is a type and suc has type Nat -> Nat", () => {
    expect(K.formatTerm(infer(natType))).toBe("Type 1");
    check(suc, sucType);
  });

  test("plus typechecks and computes", () => {
    check(plus, plusType);
    expect(K.isConvertible(env, K.app(K.app(plus, church(1)), church(1)), church(2))).toBe(true);
    expect(K.isConvertible(env, K.app(K.app(plus, church(2)), church(3)), church(5))).toBe(true);
    expect(K.isConvertible(env, K.app(suc, church(2)), church(3))).toBe(true);
  });

  test("plus one one has the normal form of the Church numeral two", () => {
    const computed = normal(K.app(K.app(plus, church(1)), church(1)));
    expect(K.isConvertible(env, computed, church(2))).toBe(true);
    // Structural check too: quoting really produced `fun A f x => f (f x)`.
    expect(computed.tag).toBe("Lam");
    if (computed.tag !== "Lam") return;
    expect(computed.body.tag).toBe("Lam");
    if (computed.body.tag !== "Lam") return;
    expect(computed.body.body.tag).toBe("Lam");
  });

  test("computing under binders normalizes the body", () => {
    const two = normal(K.app(K.app(plus, church(1)), church(1)));
    expect(K.isConvertible(env, K.app(K.app(two, K.Unit), endoId), K.app(endoId, endoId))).toBe(true);
  });
});

describe("dependent pairs", () => {
  test("a dependent pair checks against its Sigma type", () => {
    check(depPair, depSigma);
    expect(K.formatTerm(infer(depPair))).toBe(K.formatTerm(depSigma));
  });

  test("fst projects the first component's type", () => {
    // fst <Unit, fun x => x> : Type 0
    expect(K.formatTerm(infer(K.fst(depPair)))).toBe("Type 0");
  });

  test("snd projects the dependent second component", () => {
    // snd <Unit, fun x => x> : Unit -> Unit
    check(K.snd(depPair), K.pi("_", K.Unit, K.Unit));
  });

  test("pair eta: p converts to <fst p, snd p>", () => {
    const eta = K.lam("p", depSigma, K.pair(depSigma, K.fst(K.varTerm(0)), K.snd(K.varTerm(0))));
    const plain = K.lam("p", depSigma, K.varTerm(0));
    expect(K.isConvertible(env, eta, plain)).toBe(true);
    check(eta, K.pi("_", depSigma, depSigma));
  });

  test("fst of a non-pair is rejected", () => {
    expectReason(K.inferType(env, K.fst(K.tt)), "not-a-sigma");
  });

  test("And and Not are prelude definitions over Sigma and Pi", () => {
    const andUU = K.And(K.Unit, K.Unit);
    const normalAnd = normal(andUU);
    expect(normalAnd.tag).toBe("Sigma");
    expect(K.isConvertible(env, andUU, K.sigma("_", K.Unit, K.Unit))).toBe(true);
    check(K.pair(andUU, K.tt, K.tt), andUU);
    expect(K.isConvertible(env, K.Not(K.Unit), K.pi("_", K.Unit, K.Empty))).toBe(true);
    expect(K.formatTerm(infer(K.Not(K.Unit)))).toBe("Type 0");
  });
});

describe("J (transport)", () => {
  test("transport typechecks against its specification", () => {
    check(transport, transportType);
    expect(K.formatTerm(infer(transport))).toBe(K.formatTerm(transportType));
  });

  test("J computes on refl: J A a C d a (refl A a) is d", () => {
    const motive = K.lam("b", K.Unit, K.lam("p", K.Eq(K.Unit, K.tt, K.varTerm(0)), K.Unit));
    const applied = K.J(0, K.Unit, K.tt, motive, K.tt, K.tt, K.Refl(K.Unit, K.tt));
    expect(K.isConvertible(env, applied, K.tt)).toBe(true);
    check(applied, K.Unit);
  });

  test("a worked transport: sym via J", () => {
    // sym : (A : Type 0) -> (a b : A) -> Eq A a b -> Eq A b a
    const sym = K.mk(
      K.lamMk(
        "A",
        K.sortMk(0),
        K.lamMk(
          "a",
          K.varMk("A"),
          K.lamMk(
            "b",
            K.varMk("A"),
            K.lamMk(
              "p",
              K.primMk(K.OP_EQ, [K.varMk("A"), K.varMk("a"), K.varMk("b")]),
              K.primMk(
                K.OP_J,
                [
                  K.varMk("A"),
                  K.varMk("a"),
                  K.lamMk(
                    "b2",
                    K.varMk("A"),
                    K.lamMk(
                      "p2",
                      K.primMk(K.OP_EQ, [K.varMk("A"), K.varMk("a"), K.varMk("b2")]),
                      K.primMk(K.OP_EQ, [K.varMk("A"), K.varMk("b2"), K.varMk("a")]),
                    ),
                  ),
                  K.primMk(K.OP_REFL, [K.varMk("A"), K.varMk("a")]),
                  K.varMk("b"),
                  K.varMk("p"),
                ],
                0,
              ),
            ),
          ),
        ),
      ),
    );
    const symType = K.mk(
      K.piMk(
        "A",
        K.sortMk(0),
        K.piMk(
          "a",
          K.varMk("A"),
          K.piMk(
            "b",
            K.varMk("A"),
            K.piMk(
              "p",
              K.primMk(K.OP_EQ, [K.varMk("A"), K.varMk("a"), K.varMk("b")]),
              K.primMk(K.OP_EQ, [K.varMk("A"), K.varMk("b"), K.varMk("a")]),
            ),
          ),
        ),
      ),
    );
    check(sym, symType);
    expect(K.formatTerm(infer(sym))).toBe(K.formatTerm(symType));
  });

  test("sum elimination: case on an inr reduces to the right branch", () => {
    const sum = K.Sum(K.Empty, K.Unit);
    const motive = K.lam("s", sum, K.Unit);
    const onLeft = K.lam("a", K.Empty, K.Absurd(0, K.Unit, K.varTerm(0)));
    const onRight = K.lam("b", K.Unit, K.tt);
    const applied = K.SumCase(0, K.Empty, K.Unit, motive, onLeft, onRight, K.Inr(K.Empty, K.Unit, K.tt));
    check(applied, K.Unit);
    expect(K.isConvertible(env, applied, K.tt)).toBe(true);
  });
});

describe("term utilities", () => {
  test("normalize is idempotent on normal forms", () => {
    const once = normal(K.app(K.app(plus, church(2)), church(2)));
    const twice = normal(once);
    expect(K.formatTerm(once)).toBe(K.formatTerm(twice));
  });

  test("erase drops types, proofs and Sigma annotations", () => {
    expect(K.erase(K.sort(0))).toEqual({ tag: "Erased" });
    expect(K.erase(K.pi("A", K.sort(0), K.varTerm(0)))).toEqual({ tag: "Erased" });
    expect(K.erase(K.Farkas([K.tt], [1n]))).toEqual({ tag: "Erased" });
    const erased = K.erase(K.lam("x", K.Unit, K.app(K.varTerm(0), K.tt)));
    expect(erased).toEqual({
      tag: "Lam",
      name: "x",
      body: { tag: "App", fn: { tag: "Var", index: 0 }, arg: { tag: "Prim", op: "tt", args: [] } },
    });
    // Binders are preserved, so indices keep their meaning.
    expect(K.erase(K.pair(K.Unit, K.tt, K.tt))).toEqual({
      tag: "Pair",
      first: { tag: "Prim", op: "tt", args: [] },
      second: { tag: "Prim", op: "tt", args: [] },
    });
  });

  test("formatTerm prints a readable shape", () => {
    expect(K.formatTerm(K.sort(2))).toBe("Type 2");
    expect(K.formatTerm(idType)).toBe("((A : Type 0) -> ((x : A) -> A))");
    expect(K.formatTerm(K.intLit(7))).toBe("7");
    expect(K.formatTerm(K.letTerm("x", K.Unit, K.tt, K.varTerm(0)))).toBe("(let x : Unit() = tt() in x)");
  });

  test("intLit accepts numbers and bigints", () => {
    expect(K.formatTerm(K.intLit(3))).toBe("3");
    expect(K.formatTerm(K.intLit(3n))).toBe("3");
  });

  test("normalizing a term with a free variable reports an internal error, not a crash", () => {
    const error = expectErr(K.normalize(env, K.varTerm(0)));
    expect(error.reason).toBe("internal");
  });
});
