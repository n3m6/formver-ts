/**
 * Milestone 3 soundness tests: specification section 9.1. Every test here is an attempt
 * to make the kernel accept a proof of `false`, or to make conversion identify two things
 * that are not the same. Each one must be rejected.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { expectErr, expectOk, expectReason } from "./helpers";
import {
  addMk,
  andMk,
  appendMk,
  boundsProof,
  byContraMk,
  conv,
  emptyMk,
  env,
  farkasMk,
  getMk,
  intMk,
  leMk,
  leProofMk,
  ltMk,
  mulConstMk,
  subMk,
  v,
  vecMk,
} from "./helpers3";

const lit = K.intLit;
const emptyType: K.Mk = emptyMk;

describe("forged Farkas certificates", () => {
  test("a certificate with the right shape but Σλb >= 0 is rejected", () => {
    // `x <= 0` and `x >= 0` are satisfiable (x = 0), so λ = [1, 1] leaves 0, not < 0.
    const term = K.mk(
      K.lamMk(
        "x",
        intMk,
        K.lamMk(
          "h1",
          leMk(v("x"), K.intLitMk(0n)),
          K.lamMk("h2", leMk(K.intLitMk(0n), v("x")), farkasMk([v("h1"), v("h2")], [1n, 1n])),
        ),
      ),
    );
    const type = K.mk(
      K.piMk(
        "x",
        intMk,
        K.piMk(
          "h1",
          leMk(v("x"), K.intLitMk(0n)),
          K.piMk("h2", leMk(K.intLitMk(0n), v("x")), emptyType),
        ),
      ),
    );
    expectReason(K.checkType(env, term, type), "farkas-invalid");
    // ... and the same holds for the multi-atom version with a positive bound.
    const values = [
      K.evalTerm(env, K.Le(K.varTerm(0), K.intLit(3)), [K.vvar(0)]),
      K.evalTerm(env, K.Le(K.intLit(0), K.varTerm(0)), [K.vvar(0)]),
    ];
    expect(expectErr(K.checkFarkas({ hypTypes: values, coeffs: [1n, 1n] })).reason).toBe("farkas-invalid");
  });

  test("a negative multiplier is rejected", () => {
    const values = [K.evalTerm(env, K.Le(K.intLit(2), K.intLit(1)), [])];
    expect(expectErr(K.checkFarkas({ hypTypes: values, coeffs: [-1n] })).reason).toBe(
      "farkas-negative-coefficient",
    );
    const term = K.mk(
      K.lamMk("h", leMk(K.intLitMk(2n), K.intLitMk(1n)), farkasMk([v("h")], [-1n])),
    );
    expectReason(
      K.checkType(env, term, K.pi("h", K.Le(lit(2), lit(1)), K.Empty)),
      "farkas-negative-coefficient",
    );
  });

  test("a forged certificate cannot be hidden behind a well-typed helper", () => {
    // Even though `Le 2 1` really is false, the kernel only accepts the *specific*
    // multiplier vector that derives the contradiction: [1] works, [0] does not.
    const values = [K.evalTerm(env, K.Le(K.intLit(2), K.intLit(1)), [])];
    expect(expectOk(K.checkFarkas({ hypTypes: values, coeffs: [1n] }))).toBeUndefined();
    expect(expectErr(K.checkFarkas({ hypTypes: values, coeffs: [0n] })).reason).toBe("farkas-invalid");
  });
});

describe("tightening edge cases", () => {
  /** `2 * x <= b` and `2 * x >= b`, as two `Le` hypotheses about the same atom. */
  const doubledPair = (bound: bigint): K.Value[] => [
    K.evalTerm(env, K.Le(K.MulConst(lit(2), K.varTerm(0)), lit(bound)), [K.vvar(0)]),
    K.evalTerm(env, K.Le(lit(bound), K.MulConst(lit(2), K.varTerm(0))), [K.vvar(0)]),
  ];

  test("`2x <= 1` with `2x >= 1` is contradictory after tightening, and is accepted", () => {
    const hypTypes = doubledPair(1n);
    expect(K.checkCertificate(hypTypes.map(K.rowOfLe).map((row) => expectOk(row)).map(K.tightenRow), [1n, 1n])).toBe(
      true,
    );
    expect(expectOk(K.checkFarkas({ hypTypes, coeffs: [1n, 1n] }))).toBeUndefined();
    // Without tightening the very same multipliers would not refute anything.
    const rows = hypTypes.map((type) => expectOk(K.rowOfLe(type)));
    expect(K.checkCertificate(rows, [1n, 1n])).toBe(false);
  });

  test("`2x <= 2` with `2x >= 2` (satisfied by x = 1) has no accepted certificate", () => {
    const hypTypes = doubledPair(2n);
    const rows = hypTypes.map((type) => K.tightenRow(expectOk(K.rowOfLe(type))));
    for (const coefficients of [
      [0n, 0n],
      [1n, 1n],
      [2n, 2n],
      [1n, 2n],
      [3n, 1n],
    ]) {
      expect(K.checkCertificate(rows, coefficients)).toBe(false);
    }
    for (const coefficients of [[1n, 1n], [0n, 1n], [1n, 0n]]) {
      expect(expectErr(K.checkFarkas({ hypTypes, coeffs: coefficients })).reason).toBe("farkas-invalid");
    }
  });
});

describe("Farkas hypotheses must be Le", () => {
  test("an Eq hypothesis is rejected", () => {
    const term = K.mk(
      K.lamMk(
        "h",
        K.primMk(K.OP_EQ, [intMk, K.intLitMk(0n), K.intLitMk(0n)]),
        farkasMk([v("h")], [1n]),
      ),
    );
    const type = K.mk(K.piMk("h", K.primMk(K.OP_EQ, [intMk, K.intLitMk(0n), K.intLitMk(0n)]), emptyType));
    expectReason(K.checkType(env, term, type), "farkas-not-a-le-hypothesis");
  });

  test("a Unit hypothesis is rejected", () => {
    const term = K.lam("h", K.Unit, K.Farkas([K.varTerm(0)], [1n]));
    expectReason(K.checkType(env, term, K.pi("h", K.Unit, K.Empty)), "farkas-not-a-le-hypothesis");
  });
});

describe("get needs the right bounds proof", () => {
  const vector = (n: bigint): K.Term => K.Vec(K.Int, lit(n));

  test("get without a bounds proof is rejected", () => {
    const term = K.mk(K.lamMk("w", vecMk(intMk, K.intLitMk(3n)), K.primMk(K.OP_GET, [intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n)])));
    expect(expectErr(K.inferType(env, term)).reason).toBe("prim-arity");
    // A bounds proof of a *different shape* is not accepted either.
    const wrongShape = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n), leProofMk(0n, 1n)),
      ),
    );
    expect(expectErr(K.inferType(env, wrongShape)).reason).toBe("type-mismatch");
  });

  test("get with a proof of the wrong bound is rejected", () => {
    // The hypothesis is a bounds proof for a *length-7* vector (`5 < 7`), so it is not
    // the bounds proof for indexing a length-3 vector at 5.
    const term = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        K.lamMk(
          "p",
          andMk(leMk(K.intLitMk(0n), K.intLitMk(5n)), ltMk(K.intLitMk(5n), K.intLitMk(7n))),
          getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(5n), v("p")),
        ),
      ),
    );
    expect(expectErr(K.inferType(env, term)).reason).toBe("type-mismatch");
    // A correct proof for a *different* index is rejected too.
    const otherIndex = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(2n), () => boundsProof(1n, 3n)),
      ),
    );
    expect(expectErr(K.inferType(env, otherIndex)).reason).toBe("type-mismatch");
    // A correct proof for the right index is accepted.
    const good = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n), () => boundsProof(1n, 3n)),
      ),
    );
    const inferred = expectOk(K.inferType(env, good));
    // The proof's type is a well-formed type, and the vector type it mentions is too.
    expect(K.isTypeTerm(env, inferred).ok).toBe(true);
    expect(K.isTypeTerm(env, vector(3n)).ok).toBe(true);
  });
});

describe("fixWf requires a decrease proof", () => {
  const motive = (): K.Mk => K.lamMk("_", intMk, intMk);
  const ihType = (x: string, le: K.Mk, lt: K.Mk): K.Mk =>
    K.piMk("y", intMk, K.piMk("py", le, K.piMk("d", lt, intMk)));
  const measureSelf = (): K.Mk => K.lamMk("z", intMk, v("z"));
  const fixAt = (step: K.Mk): K.Term =>
    K.mk(K.primMk(K.OP_FIX_WF, [intMk, motive(), measureSelf(), step, K.intLitMk(5n), leProofMk(0n, 5n)], 0));

  /** The real IH type for `x`: `(y : Int) -> Le 0 y -> Lt y x -> Int`. */
  const goodIh = (): K.Mk =>
    K.piMk(
      "y",
      intMk,
      K.piMk("py", leMk(K.intLitMk(0n), v("y")), K.piMk("d", ltMk(v("y"), v("x")), intMk)),
    );

  test("calling the induction hypothesis without the decrease proof is rejected", () => {
    const step = K.lamMk(
      "x",
      intMk,
      K.lamMk(
        "px",
        leMk(K.intLitMk(0n), v("x")),
        K.lamMk(
          "ih",
          goodIh(),
          K.appManyMk(v("ih"), [subMk(v("x"), K.intLitMk(1n)), v("px")]),
        ),
      ),
    );
    expect(expectErr(K.inferType(env, fixAt(step))).reason).toBe("type-mismatch");
  });

  test("calling it with `Le (m y) (m x)` instead of `Lt (m y) (m x)` is rejected", () => {
    const step = K.lamMk(
      "x",
      intMk,
      K.lamMk(
        "px",
        leMk(K.intLitMk(0n), v("x")),
        K.lamMk(
          "ih",
          goodIh(),
          K.appManyMk(v("ih"), [
            subMk(v("x"), K.intLitMk(1n)),
            v("px"),
            // `Le (x - 1) x` is true but is not the strict decrease proof.
            K.primMk(K.OP_BY_CONTRA, [
              subMk(v("x"), K.intLitMk(1n)),
              v("x"),
              K.lamMk("k", ltMk(v("x"), subMk(v("x"), K.intLitMk(1n))), farkasMk([v("k")], [1n])),
            ]),
          ]),
        ),
      ),
    );
    expect(expectErr(K.inferType(env, fixAt(step))).reason).toBe("type-mismatch");
  });

  test("a step of the wrong shape is rejected", () => {
    // `step` must take `x`, the non-negativity proof and the induction hypothesis.
    const tooShort = K.lamMk("x", intMk, K.intLitMk(0n));
    expect(expectErr(K.inferType(env, fixAt(tooShort))).reason).toBe("type-mismatch");
  });
});

describe("conversion must not identify distinct things", () => {
  test("Vec A n is not Vec A (n + 1)", () => {
    const plain = K.mk(K.lamMk("n", intMk, vecMk(intMk, v("n"))));
    const next = K.mk(K.lamMk("n", intMk, vecMk(intMk, addMk(v("n"), K.intLitMk(1n)))));
    expect(conv(plain, next)).toBe(false);
  });

  test("2 * x is not x + 1", () => {
    const twice = K.mk(K.lamMk("x", intMk, mulConstMk(2n, v("x"))));
    const plusOne = K.mk(K.lamMk("x", intMk, addMk(v("x"), K.intLitMk(1n))));
    expect(conv(twice, plusOne)).toBe(false);
  });

  test("Le a b is not Le a (b + 1)", () => {
    const base = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), v("b")))));
    const shifted = K.mk(K.lamMk("a", intMk, K.lamMk("b", intMk, leMk(v("a"), addMk(v("b"), K.intLitMk(1n))))));
    expect(conv(base, shifted)).toBe(false);
  });

  test("a fixWf application is not convertible with its unfolding", () => {
    const step = K.lamMk(
      "x",
      intMk,
      K.lamMk(
        "px",
        leMk(K.intLitMk(0n), v("x")),
        K.lamMk(
          "ih",
          K.piMk(
            "y",
            intMk,
            K.piMk("py", leMk(K.intLitMk(0n), v("y")), K.piMk("d", ltMk(v("y"), v("x")), intMk)),
          ),
          K.intLitMk(42n),
        ),
      ),
    );
    const applied = K.mk(
      K.primMk(
        K.OP_FIX_WF,
        [intMk, K.lamMk("_", intMk, intMk), K.lamMk("z", intMk, v("z")), step, K.intLitMk(5n), leProofMk(0n, 5n)],
        0,
      ),
    );
    // If conversion unfolded the application, this would be `42`.
    expect(conv(applied, lit(42))).toBe(false);
    expect(conv(applied, lit(0))).toBe(false);
    // `refl` at `fixWf ... 5 p` is not a proof of `Eq Int (fixWf ... 5 p) 42`: the
    // conversion that would be needed does not happen, and the check terminates.
    const reflType = K.Eq(K.Int, applied, K.intLit(42));
    expectReason(K.checkType(env, K.Refl(K.Int, applied), reflType), "type-mismatch");
    expect(conv(applied, applied)).toBe(true);
  });
});

describe("universes and self-application", () => {
  test("Type 0 : Type 0 is rejected", () => {
    expectReason(K.checkType(env, K.sort(0), K.sort(0)), "type-mismatch");
    expectReason(K.checkType(env, K.sort(1), K.sort(1)), "type-mismatch");
  });

  test("a Girard-style self-application is rejected", () => {
    const delta = K.lam("x", K.sort(0), K.app(K.varTerm(0), K.varTerm(0)));
    expectReason(K.inferType(env, delta), "not-a-function");
    expectReason(K.inferType(env, K.app(delta, delta)), "not-a-function");
  });
});

describe("ifLe and byContra directions", () => {
  test("ifLe with swapped branch hypothesis types is rejected", () => {
    const swapped = K.IfLe(
      0,
      K.Int,
      lit(1),
      lit(2),
      // `yes` must take `Le 1 2`, and `no` must take `Lt 2 1`: here they are swapped.
      K.lam("_", K.Lt(lit(2), lit(1)), lit(10)),
      K.lam("_", K.Le(lit(1), lit(2)), lit(20)),
    );
    expect(expectErr(K.inferType(env, swapped)).reason).toBe("type-mismatch");
    // The same swap on a stuck ifLe.
    const stuck = K.mk(
      K.lamMk(
        "a",
        intMk,
        K.primMk(
          K.OP_IF_LE,
          [
            intMk,
            v("a"),
            K.intLitMk(2n),
            K.lamMk("_", ltMk(K.intLitMk(2n), v("a")), K.intLitMk(10n)),
            K.lamMk("_", leMk(v("a"), K.intLitMk(2n)), K.intLitMk(20n)),
          ],
          0,
        ),
      ),
    );
    expect(expectErr(K.inferType(env, stuck)).reason).toBe("type-mismatch");
  });

  test("byContra with a hypothesis of the wrong direction is rejected", () => {
    const wrong = K.mk(
      K.lamMk(
        "k",
        ltMk(K.intLitMk(0n), K.intLitMk(1n)),
        byContraMk(K.intLitMk(0n), K.intLitMk(1n), v("k")),
      ),
    );
    expect(expectErr(K.inferType(env, wrong)).reason).toBe("type-mismatch");
    // The right direction is accepted.
    const right = byContraMk(
      K.intLitMk(0n),
      K.intLitMk(1n),
      K.lamMk("k", ltMk(K.intLitMk(1n), K.intLitMk(0n)), farkasMk([v("k")], [1n])),
    );
    expect(K.checkType(env, K.mk(right), K.Le(lit(0), lit(1))).ok).toBe(true);
    // A refutation whose domain is some *other* false proposition (here `2 < 0`) is a
    // perfectly good proof of `Le 2 0`, but it is not a refutation of `Lt 1 0`.
    const wrongRefutation = K.mk(
      byContraMk(
        K.intLitMk(0n),
        K.intLitMk(1n),
        K.lamMk("h", ltMk(K.intLitMk(2n), K.intLitMk(0n)), farkasMk([v("h")], [1n])),
      ),
    );
    expect(expectErr(K.inferType(env, wrongRefutation)).reason).toBe("type-mismatch");
  });
});

describe("append and slice bounds are not free", () => {
  test("append without its length proof is rejected", () => {
    const term = K.mk(
      K.lamMk(
        "u",
        vecMk(intMk, K.intLitMk(2n)),
        K.lamMk(
          "w",
          vecMk(intMk, K.intLitMk(3n)),
          K.primMk(K.OP_APPEND, [intMk, K.intLitMk(2n), K.intLitMk(3n), v("u"), v("w")]),
        ),
      ),
    );
    expect(expectErr(K.inferType(env, term)).reason).toBe("prim-arity");
  });

  test("a wrong append bound is rejected", () => {
    const term = K.mk(
      K.lamMk(
        "u",
        vecMk(intMk, K.intLitMk(2n)),
        K.lamMk(
          "w",
          vecMk(intMk, K.intLitMk(3n)),
          appendMk(intMk, K.intLitMk(2n), K.intLitMk(3n), v("u"), v("w"), leProofMk(0n, 4n)),
        ),
      ),
    );
    expect(expectErr(K.inferType(env, term)).reason).toBe("type-mismatch");
  });
});
