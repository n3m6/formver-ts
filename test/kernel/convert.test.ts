/**
 * Definitional equality: beta, eta (functions and pairs), delta (definitions unfold,
 * opaque ones do not), zeta, and the primitive conversion hooks (`convArgs`,
 * `irrelevant`).
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { church, endoId, expectOk, plus, plusType, transport, transportType } from "./helpers";

const base = K.emptyEnv();

const unitToUnit: K.Term = K.pi("_", K.Unit, K.Unit);

/** Adds a non-opaque definition `def : type = value` on top of `env`. */
function withDef(env: K.Env, name: string, type: K.Term, value: K.Term, opaque?: boolean): K.Env {
  const decl: K.Decl = opaque === undefined
    ? { kind: "def", name, type, value }
    : { kind: "def", name, type, value, opaque };
  return expectOk(K.addDecl(env, decl));
}

describe("beta", () => {
  test("(fun x => x) tt converts to tt", () => {
    expect(K.isConvertible(base, K.app(endoId, K.tt), K.tt)).toBe(true);
  });

  test("(fun x y => x) tt tt converts to tt and ignores the second argument", () => {
    const first = K.lam("x", K.Unit, K.lam("y", K.Unit, K.varTerm(1)));
    const applied = K.app(K.app(first, K.tt), K.tt);
    expect(K.isConvertible(base, applied, K.tt)).toBe(true);
  });

  test("beta is captured-argument safe: (fun x => fun y => x) y first", () => {
    // Under a lambda, `(fun x => fun y => x) y` must be `fun z => y`, not `fun z => z`.
    const term = K.lam(
      "y",
      K.Unit,
      K.app(K.lam("x", K.Unit, K.lam("z", K.Unit, K.varTerm(1))), K.varTerm(0)),
    );
    const expected = K.lam("y", K.Unit, K.lam("z", K.Unit, K.varTerm(1)));
    expect(K.isConvertible(base, term, expected)).toBe(true);
  });

  test("normalization performs beta under binders", () => {
    const computed = expectOk(K.normalize(base, K.app(K.app(plus, church(1)), church(1))));
    expect(K.isConvertible(base, computed, church(2))).toBe(true);
  });
});

describe("eta", () => {
  test("functions: fun x => f x converts to f", () => {
    const eta = K.lam("f", unitToUnit, K.lam("x", K.Unit, K.app(K.varTerm(1), K.varTerm(0))));
    const plain = K.lam("f", unitToUnit, K.varTerm(0));
    expect(K.isConvertible(base, eta, plain)).toBe(true);
    expect(K.isConvertible(base, plain, eta)).toBe(true);
  });

  test("pairs: p converts to <fst p, snd p>, in both directions", () => {
    const andUU = K.And(K.Unit, K.Unit);
    const eta = K.lam("p", andUU, K.pair(andUU, K.fst(K.varTerm(0)), K.snd(K.varTerm(0))));
    const plain = K.lam("p", andUU, K.varTerm(0));
    expect(K.isConvertible(base, eta, plain)).toBe(true);
    expect(K.isConvertible(base, plain, eta)).toBe(true);
    // The pair's Sigma annotation does not affect equality.
    const otherAnnotation = K.lam(
      "p",
      andUU,
      K.pair(K.sigma("_", K.Unit, K.Unit), K.fst(K.varTerm(0)), K.snd(K.varTerm(0))),
    );
    expect(K.isConvertible(base, otherAnnotation, plain)).toBe(true);
  });

  test("eta does not identify distinct functions", () => {
    const f = K.lam("f", unitToUnit, K.lam("x", K.Unit, K.varTerm(1)));
    const g = K.lam("f", unitToUnit, K.lam("x", K.Unit, K.varTerm(0)));
    expect(K.isConvertible(base, f, g)).toBe(false);
  });

  test("eta does not identify distinct pairs", () => {
    const left = K.lam("p", K.And(K.Unit, K.Unit), K.fst(K.varTerm(0)));
    const right = K.lam("p", K.And(K.Unit, K.Unit), K.snd(K.varTerm(0)));
    expect(K.isConvertible(base, left, right)).toBe(false);
  });
});

describe("delta", () => {
  const myId = withDef(base, "myId", unitToUnit, endoId);

  test("a definition unfolds", () => {
    expect(K.isConvertible(myId, K.constTerm("myId"), endoId)).toBe(true);
    expect(K.isConvertible(myId, K.app(K.constTerm("myId"), K.tt), K.tt)).toBe(true);
  });

  test("an opaque definition does not unfold", () => {
    const opaqueEnv = withDef(base, "opaqueId", unitToUnit, endoId, true);
    expect(K.isConvertible(opaqueEnv, K.constTerm("opaqueId"), endoId)).toBe(false);
    expect(K.isConvertible(opaqueEnv, K.constTerm("opaqueId"), K.constTerm("opaqueId"))).toBe(true);
    // It still has its declared type.
    expect(K.formatTerm(expectOk(K.inferType(opaqueEnv, K.constTerm("opaqueId"))))).toBe(
      K.formatTerm(unitToUnit),
    );
    expect(K.isConvertible(opaqueEnv, K.app(K.constTerm("opaqueId"), K.tt), K.tt)).toBe(false);
  });

  test("an axiom is opaque", () => {
    const axiomEnv = expectOk(
      K.addDecl(base, { kind: "axiom", name: "trusted", type: unitToUnit, reason: "test fixture" }),
    );
    expect(K.isConvertible(axiomEnv, K.constTerm("trusted"), endoId)).toBe(false);
    expect(K.axiomsUsed(axiomEnv)).toEqual(["trusted"]);
  });

  test("delta unfolds nested definitions and prelude definitions", () => {
    const nested = withDef(myId, "myIdTwice", unitToUnit, K.constTerm("myId"));
    expect(K.isConvertible(nested, K.constTerm("myIdTwice"), endoId)).toBe(true);
    // `And A B` unfolds to a non-dependent Sigma.
    expect(K.isConvertible(base, K.And(K.Unit, K.Unit), K.sigma("_", K.Unit, K.Unit))).toBe(true);
    expect(K.isConvertible(base, K.Not(K.Unit), K.pi("_", K.Unit, K.Empty))).toBe(true);
  });

  test("an unknown constant is neutral, and distinct names differ", () => {
    expect(K.isConvertible(base, K.constTerm("nope"), K.constTerm("nope"))).toBe(true);
    expect(K.isConvertible(base, K.constTerm("nope"), K.constTerm("other"))).toBe(false);
    expect(K.isConvertible(base, K.constTerm("nope"), K.tt)).toBe(false);
  });

  test("opaque definitions keep conversion terminating: a self-application of fixWf-style names never unfolds", () => {
    // `opaqueId (opaqueId)` is ill-typed, but conversion must still answer instead of
    // unfolding forever.
    const opaqueEnv = withDef(base, "opaqueId", unitToUnit, endoId, true);
    const term = K.app(K.constTerm("opaqueId"), K.constTerm("opaqueId"));
    expect(K.isConvertible(opaqueEnv, term, term)).toBe(true);
  });
});

describe("zeta", () => {
  test("let x = a in b converts to b[a/x]", () => {
    expect(K.isConvertible(base, K.letTerm("x", K.Unit, K.tt, K.varTerm(0)), K.tt)).toBe(true);
    expect(
      K.isConvertible(
        base,
        K.letTerm("x", unitToUnit, endoId, K.app(K.varTerm(0), K.tt)),
        K.app(endoId, K.tt),
      ),
    ).toBe(true);
  });

  test("let is transparent to typing", () => {
    const term = K.letTerm("x", K.Unit, K.tt, K.varTerm(0));
    expect(expectOk(K.checkType(base, term, K.Unit))).toBeUndefined();
    expect(K.formatTerm(expectOk(K.inferType(base, term)))).toBe("Unit()");
    const bad = K.letTerm("x", K.Unit, K.tt, K.varTerm(0));
    expect(K.checkType(base, bad, K.Empty).ok).toBe(false);
  });

  test("a let-bound variable does not shadow the outer one incorrectly", () => {
    // fun y => let x = y in (fun y => x) : Unit -> Unit
    const term = K.lam(
      "y",
      K.Unit,
      K.letTerm("x", K.Unit, K.varTerm(0), K.lam("y", K.Unit, K.varTerm(1))),
    );
    expect(K.isConvertible(base, term, K.lam("y", K.Unit, K.lam("z", K.Unit, K.varTerm(1))))).toBe(
      true,
    );
    expect(K.checkType(base, term, K.pi("_", K.Unit, unitToUnit)).ok).toBe(true);
  });

  test("let-bound definitions are usable in types", () => {
    // let A = Unit in (tt : A) typechecks.
    const term = K.letTerm("A", K.sort(0), K.Unit, K.tt);
    expect(K.checkType(base, term, K.Unit).ok).toBe(true);
  });
});

describe("primitive conversion hooks", () => {
  const info: K.PrimInfo = {
    name: "Test",
    arity: 2,
    typeFor: () => K.sort(0),
    irrelevant: [1],
  };
  const eq = (x: K.Value, y: K.Value): boolean => x === y;
  const a: K.Value = { tag: "Sort", level: 0 };
  const b: K.Value = { tag: "Sort", level: 0 };
  const c: K.Value = { tag: "Sort", level: 1 };

  test("irrelevant positions are skipped", () => {
    expect(K.convPrimArgs(info, [a, b], [a, c], eq)).toBe(true);
    expect(K.convPrimArgs(info, [a, b], [c, b], eq)).toBe(false);
  });

  test("arity mismatch fails", () => {
    expect(K.convPrimArgs(info, [a], [a, b], eq)).toBe(false);
  });

  test("convArgs decides when it returns a verdict and defers when it returns undefined", () => {
    const strict: K.PrimInfo = { ...info, convArgs: () => false };
    expect(K.convPrimArgs(strict, [a, b], [a, b], eq)).toBe(false);
    const lenient: K.PrimInfo = { ...info, convArgs: () => true };
    expect(K.convPrimArgs(lenient, [a, b], [c, c], eq)).toBe(true);
    const undecided: K.PrimInfo = { ...info, convArgs: () => undefined };
    expect(K.convPrimArgs(undecided, [a, b], [c, b], eq)).toBe(false);
    expect(K.convPrimArgs(undecided, [a, b], [a, c], eq)).toBe(true);
  });

  test("an unknown op falls back to argument-wise comparison", () => {
    expect(K.convPrimArgs(undefined, [a], [a], eq)).toBe(true);
    expect(K.convPrimArgs(undefined, [a], [c], eq)).toBe(false);
  });

  test("`Le` converts by the linear normal form of `b - a`", () => {
    expect(K.isConvertible(base, K.Le(K.intLit(2), K.intLit(1)), K.Le(K.intLit(2), K.intLit(1)))).toBe(true);
    // `Le 1 2` and `Le 2 3` are the same proposition: `b - a` is 1 for both.
    expect(K.isConvertible(base, K.Le(K.intLit(1), K.intLit(2)), K.Le(K.intLit(2), K.intLit(3)))).toBe(true);
    // ... and it must never identify different bounds.
    expect(K.isConvertible(base, K.Le(K.intLit(2), K.intLit(1)), K.Le(K.intLit(2), K.intLit(2)))).toBe(false);
    expect(K.isConvertible(base, K.Le(K.intLit(1), K.intLit(2)), K.Le(K.intLit(1), K.intLit(3)))).toBe(false);
  });

  test("proof irrelevance is expressible through the registry shape", () => {
    // Milestone 3 marks proof arguments (for example the bounds proof of `get`) this way.
    const withProof: K.PrimInfo = { ...info, irrelevant: [2] };
    const d: K.Value = { tag: "Sort", level: 2 };
    // Position 2 is ignored, positions 0 and 1 are not.
    expect(K.convPrimArgs(withProof, [a, b, c], [a, b, d], eq)).toBe(true);
    expect(K.convPrimArgs(withProof, [a, b, c], [a, c, d], eq)).toBe(false);
    expect(K.convPrimArgs(withProof, [a, b, c], [d, b, c], eq)).toBe(false);
  });
});

describe("conversion does not confuse distinct types", () => {
  test("Sigma with different components differs", () => {
    expect(K.isConvertible(base, K.sigma("_", K.Unit, K.Unit), K.sigma("_", K.Unit, K.Empty))).toBe(false);
  });

  test("Pi with different codomains differs", () => {
    expect(K.isConvertible(base, K.pi("_", K.Unit, K.Unit), K.pi("_", K.Unit, K.Empty))).toBe(false);
  });

  test("Type levels are not cumulative", () => {
    expect(K.isConvertible(base, K.sort(0), K.sort(1))).toBe(false);
  });

  test("distinct integer literals differ", () => {
    expect(K.isConvertible(base, K.intLit(2), K.intLit(3))).toBe(false);
    expect(K.isConvertible(base, K.intLit(3), K.intLit(3))).toBe(true);
  });

  test("distinct prims differ by op and by level", () => {
    expect(K.isConvertible(base, K.Empty, K.Unit)).toBe(false);
    const absurd0 = K.Absurd(0, K.Unit, K.tt);
    const absurd1 = K.Absurd(1, K.Unit, K.tt);
    expect(K.isConvertible(base, absurd0, absurd0)).toBe(true);
    expect(K.isConvertible(base, absurd0, absurd1)).toBe(false);
  });

  test("transport is not accidentally convertible with the identity function", () => {
    expect(K.isConvertible(base, transport, K.lam("x", K.Unit, K.varTerm(0)))).toBe(false);
    expect(K.isConvertible(base, transport, transport)).toBe(true);
    expect(K.formatTerm(expectOk(K.inferType(base, transport)))).toBe(K.formatTerm(transportType));
  });

  test("plus is not convertible with a function of the wrong shape", () => {
    expect(K.isConvertible(base, plus, K.lam("x", K.Unit, K.varTerm(0)))).toBe(false);
    expect(K.formatTerm(expectOk(K.inferType(base, plus)))).toBe(K.formatTerm(plusType));
  });
});
