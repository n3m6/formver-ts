/**
 * The Farkas rule: GCD tightening, the certificate arithmetic, and the rejections of
 * specification section 9.1 that apply to milestone 2's literal fragment.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { expectErr, expectOk } from "./helpers";
import { addMk, byContraMk, farkasMk, intMk, leMk, ltMk, v } from "./helpers3";

const env = K.emptyEnv();

const row = (a: Record<string, bigint>, b: bigint): K.Row => ({ a, b });

describe("floorDiv and gcd", () => {
  test("floor division rounds toward negative infinity", () => {
    expect(K.floorDiv(1n, 2n)).toBe(0n);
    expect(K.floorDiv(-1n, 2n)).toBe(-1n);
    expect(K.floorDiv(-3n, 2n)).toBe(-2n);
    expect(K.floorDiv(4n, 2n)).toBe(2n);
    expect(K.floorDiv(-4n, 2n)).toBe(-2n);
    expect(K.floorDiv(7n, 1n)).toBe(7n);
  });

  test("gcd is non-negative", () => {
    expect(K.gcd(4n, 6n)).toBe(2n);
    expect(K.gcd(-4n, 6n)).toBe(2n);
    expect(K.gcd(0n, 5n)).toBe(5n);
    expect(K.gcd(0n, 0n)).toBe(0n);
  });
});

describe("tightenRow", () => {
  test("divides coefficients by the GCD and floors the bound", () => {
    expect(K.tightenRow(row({ x: 2n }, 1n))).toEqual(row({ x: 1n }, 0n));
    expect(K.tightenRow(row({ x: -2n }, -1n))).toEqual(row({ x: -1n }, -1n));
    expect(K.tightenRow(row({ x: 4n, y: -6n }, 3n))).toEqual(row({ x: 2n, y: -3n }, 1n));
  });

  test("leaves rows with GCD 1 alone and drops zero coefficients", () => {
    expect(K.tightenRow(row({ x: 3n, y: 2n }, 5n))).toEqual(row({ x: 3n, y: 2n }, 5n));
    expect(K.tightenRow(row({ x: 3n, y: 0n }, 5n))).toEqual(row({ x: 1n }, 1n));
    expect(K.tightenRow(row({}, 4n))).toEqual(row({}, 4n));
    expect(K.tightenRow(row({}, -4n))).toEqual(row({}, -4n));
  });

  test("tightening is what makes a strict pair contradictory", () => {
    // 2x <= 1 and 2x >= 1 tighten to x <= 0 and -x <= -1, which are contradictory.
    const rows = [row({ x: 2n }, 1n), row({ x: -2n }, -1n)];
    expect(K.checkCertificate(rows.map(K.tightenRow), [1n, 1n])).toBe(true);
    // Without tightening they are not refuted by this certificate.
    expect(K.checkCertificate(rows, [1n, 1n])).toBe(false);
  });

  test("2x <= 2 and 2x >= 2 are satisfiable and stay unrefuted", () => {
    const rows = [row({ x: 2n }, 2n), row({ x: -2n }, -2n)];
    const tightened = rows.map(K.tightenRow);
    expect(tightened).toEqual([row({ x: 1n }, 1n), row({ x: -1n }, -1n)]);
    expect(K.checkCertificate(tightened, [1n, 1n])).toBe(false);
    expect(K.checkCertificate(tightened, [0n, 0n])).toBe(false);
    expect(K.checkCertificate(tightened, [1n, 1n, 1n])).toBe(false);
  });
});

describe("checkCertificate", () => {
  const contradictory = [row({ x: 1n }, 1n), row({ x: -1n }, -2n)];

  test("accepts a genuine refutation", () => {
    expect(K.checkCertificate(contradictory, [1n, 1n])).toBe(true);
    expect(K.checkCertificate(contradictory, [2n, 2n])).toBe(true);
    // x <= 1 together with x >= 1 is satisfiable (x = 1), so it is not a refutation.
    expect(K.checkCertificate([row({ x: 1n }, 1n), row({ x: -1n }, -1n)], [1n, 1n])).toBe(false);
  });

  test("rejects a forged certificate whose bound is non-negative", () => {
    // Right shape, but Σ λ b >= 0: no contradiction.
    expect(K.checkCertificate([row({ x: 1n }, 1n), row({ x: -1n }, 0n)], [1n, 1n])).toBe(false);
    expect(K.checkCertificate([row({}, 0n)], [1n])).toBe(false);
    expect(K.checkCertificate([], [])).toBe(false);
  });

  test("rejects negative multipliers", () => {
    expect(K.checkCertificate(contradictory, [-1n, 1n])).toBe(false);
    expect(K.checkCertificate(contradictory, [1n, -1n])).toBe(false);
  });

  test("rejects uncancelled atoms", () => {
    expect(K.checkCertificate([row({ x: 1n, y: 1n }, -1n)], [1n])).toBe(false);
    expect(K.checkCertificate([row({ x: 1n }, -1n), row({ y: -1n }, -1n)], [1n, 1n])).toBe(false);
  });

  test("rejects a coefficient count mismatch", () => {
    expect(K.checkCertificate(contradictory, [1n])).toBe(false);
    expect(K.checkCertificate([row({ x: 1n }, 1n)], [1n, 1n])).toBe(false);
  });

  test("atom names that collide with Object prototype members are handled safely", () => {
    // `Object.fromEntries` creates a real own property called `__proto__`, unlike an
    // object literal, so this genuinely exercises the atom map.
    const protoRow = (coefficient: bigint, b: bigint): K.Row => ({
      a: Object.fromEntries([["__proto__", coefficient]]),
      b,
    });
    expect(K.tightenRow(protoRow(2n, 1n))).toEqual(protoRow(1n, 0n));
    expect(K.checkCertificate([protoRow(1n, 1n), protoRow(-1n, -2n)], [1n, 1n])).toBe(true);
    expect(K.checkCertificate([protoRow(1n, 1n), protoRow(-1n, -1n)], [1n, 1n])).toBe(false);
  });
});

describe("checkFarkas", () => {
  const le = (a: number, b: number): K.Term => K.Le(K.intLit(a), K.intLit(b));
  /** The rule takes the hypotheses' inferred *types* as values, as `check.ts` passes them. */
  const hyp = (...types: K.Term[]): K.Value[] => types.map((type) => K.evalTerm(env, type, []));

  test("accepts a contradictory literal hypothesis", () => {
    expect(expectOk(K.checkFarkas({ hypTypes: hyp(le(2, 1)), coeffs: [1n] }))).toBeUndefined();
    expect(expectOk(K.checkFarkas({ hypTypes: hyp(le(0, -1)), coeffs: [5n] }))).toBeUndefined();
  });

  test("rejects a satisfiable hypothesis", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: hyp(le(2, 2)), coeffs: [1n] })).reason).toBe("farkas-invalid");
    expect(expectErr(K.checkFarkas({ hypTypes: hyp(le(1, 2)), coeffs: [1n] })).reason).toBe("farkas-invalid");
  });

  test("rejects hypotheses that are not `Le`", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [K.evalTerm(env, K.Unit, [])], coeffs: [1n] })).reason).toBe(
      "farkas-not-a-le-hypothesis",
    );
    expect(
      expectErr(K.checkFarkas({ hypTypes: hyp(K.Eq(K.Unit, K.tt, K.tt)), coeffs: [1n] })).reason,
    ).toBe("farkas-not-a-le-hypothesis");
  });

  test("rejects a coefficient count mismatch and negative coefficients", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: hyp(le(2, 1)), coeffs: [1n, 1n] })).reason).toBe("farkas-shape");
    expect(expectErr(K.checkFarkas({ hypTypes: hyp(le(2, 1), le(2, 1)), coeffs: [1n] })).reason).toBe("farkas-shape");
    expect(expectErr(K.checkFarkas({ hypTypes: hyp(le(2, 1)), coeffs: [-1n] })).reason).toBe(
      "farkas-negative-coefficient",
    );
  });

  test("builds rows over atoms from the linear normal form of s - t", () => {
    // `Le x 0` is the row `x <= 0`, so a single multiplier cannot cancel its atom.
    const xAt = K.evalTerm(env, K.Le(K.varTerm(0), K.intLit(0)), [K.vvar(0)]);
    const row = expectOk(K.rowOfLe(xAt));
    expect(row.b).toBe(0n);
    expect(Object.values(row.a)).toEqual([1n]);
    expect(expectErr(K.checkFarkas({ hypTypes: [xAt], coeffs: [1n] })).reason).toBe("farkas-invalid");
    // `Le x x` is the row `0 <= 0`: no atom at all, and no contradiction either.
    const xLeX = K.evalTerm(env, K.Le(K.varTerm(0), K.varTerm(0)), [K.vvar(0)]);
    expect(expectOk(K.rowOfLe(xLeX))).toEqual({ a: {}, b: 0n });
  });

  test("rows over atoms: `-2x <= 0` together with `2x <= 0` refutes nothing", () => {
    // `Le (-x) x` is the row `-2x <= 0` and `Le x (-x)` is `2x <= 0`; x = 0 satisfies
    // both, so no multiplier can derive a contradiction.
    const openLe = (lhs: K.Term, rhs: K.Term): K.Value => K.evalTerm(env, K.Le(lhs, rhs), [K.vvar(0)]);
    const negX = K.Neg(K.varTerm(0));
    const rows = [openLe(negX, K.varTerm(0)), openLe(K.varTerm(0), negX)];
    const row = expectOk(K.rowOfLe(rows[0]!));
    expect(row.b).toBe(0n);
    expect(Object.values(row.a)).toEqual([-2n]);
    expect(expectErr(K.checkFarkas({ hypTypes: rows, coeffs: [1n, 1n] })).reason).toBe("farkas-invalid");
    // With the *strict* versions (`Lt`), integer tightening makes them contradictory.
    const strict = [
      K.evalTerm(env, K.Lt(negX, K.varTerm(0)), [K.vvar(0)]),
      K.evalTerm(env, K.Lt(K.varTerm(0), negX), [K.vvar(0)]),
    ];
    expect(expectOk(K.checkFarkas({ hypTypes: strict, coeffs: [1n, 1n] }))).toBeUndefined();
  });

  test("an empty hypothesis list cannot prove false", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [], coeffs: [] })).reason).toBe("farkas-invalid");
  });
});

describe("real certificates over atoms", () => {
  // The bounds VC: from `0 <= i` and `i < n`, prove `i + 1 <= n`.
  const boundsType = K.mk(
    K.piMk(
      "i",
      intMk,
      K.piMk(
        "n",
        intMk,
        K.piMk(
          "h1",
          leMk(K.intLitMk(0n), v("i")),
          K.piMk("h2", ltMk(v("i"), v("n")), leMk(addMk(v("i"), K.intLitMk(1n)), v("n"))),
        ),
      ),
    ),
  );
  const boundsTerm = K.mk(
    K.lamMk(
      "i",
      intMk,
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "h1",
          leMk(K.intLitMk(0n), v("i")),
          K.lamMk(
            "h2",
            ltMk(v("i"), v("n")),
            byContraMk(
              addMk(v("i"), K.intLitMk(1n)),
              v("n"),
              K.lamMk(
                "k",
                ltMk(v("n"), addMk(v("i"), K.intLitMk(1n))),
                farkasMk([v("h1"), v("h2"), v("k")], [0n, 1n, 1n]),
              ),
            ),
          ),
        ),
      ),
    ),
  );

  test("the bounds VC is accepted with the multipliers [0, 1, 1]", () => {
    // The rows, in the kernel's convention: `0 - i <= 0`, `(i + 1) - n <= -1` and
    // `(n + 1) - (i + 1) <= 0`; λ = [0, 1, 1] cancels both atoms and leaves -1.
    const i = K.vvar(0);
    const n = K.vvar(1);
    const hypTypes = [
      K.evalTerm(env, K.Le(K.intLit(0), K.varTerm(1)), [i, n]),
      K.evalTerm(env, K.Lt(K.varTerm(1), K.varTerm(0)), [i, n]),
      K.evalTerm(env, K.Lt(K.varTerm(0), K.Add(K.varTerm(1), K.intLit(1))), [i, n]),
    ];
    expect(expectOk(K.checkFarkas({ hypTypes, coeffs: [0n, 1n, 1n] }))).toBeUndefined();
    // Any other multiplier vector is rejected.
    expect(expectErr(K.checkFarkas({ hypTypes, coeffs: [1n, 1n, 1n] })).reason).toBe("farkas-invalid");
    expect(K.checkType(env, boundsTerm, boundsType).ok).toBe(true);
  });

  test("a certificate for a `clamp` path is accepted", () => {
    // From `x + 1 <= lo` and `lo <= hi`, conclude `x <= hi`: rows `x - lo <= -1`,
    // `lo - hi <= 0`, `hi - x <= -1`, and λ = [1, 1, 1] leaves -2.
    const type = K.mk(
      K.piMk(
        "x",
        intMk,
        K.piMk(
          "lo",
          intMk,
          K.piMk(
            "hi",
            intMk,
            K.piMk(
              "h1",
              leMk(addMk(v("x"), K.intLitMk(1n)), v("lo")),
              K.piMk("pre", leMk(v("lo"), v("hi")), leMk(v("x"), v("hi"))),
            ),
          ),
        ),
      ),
    );
    const term = K.mk(
      K.lamMk(
        "x",
        intMk,
        K.lamMk(
          "lo",
          intMk,
          K.lamMk(
            "hi",
            intMk,
            K.lamMk(
              "h1",
              leMk(addMk(v("x"), K.intLitMk(1n)), v("lo")),
              K.lamMk(
                "pre",
                leMk(v("lo"), v("hi")),
                byContraMk(
                  v("x"),
                  v("hi"),
                  K.lamMk("k", ltMk(v("hi"), v("x")), farkasMk([v("h1"), v("pre"), v("k")], [1n, 1n, 1n])),
                ),
              ),
            ),
          ),
        ),
      ),
    );
    expect(K.checkType(env, term, type).ok).toBe(true);
  });

  test("the `?1` obligation of the clamp skeleton: Le lo lo", () => {
    // λ = [0, 1]: the first hypothesis is unused, and `Lt lo lo` is refuted on its own.
    const type = K.mk(
      K.piMk(
        "lo",
        intMk,
        K.piMk(
          "h1",
          leMk(addMk(v("lo"), K.intLitMk(1n)), v("lo")),
          leMk(v("lo"), v("lo")),
        ),
      ),
    );
    const term = K.mk(
      K.lamMk(
        "lo",
        intMk,
        K.lamMk(
          "h1",
          leMk(addMk(v("lo"), K.intLitMk(1n)), v("lo")),
          byContraMk(
            v("lo"),
            v("lo"),
            K.lamMk("k", ltMk(v("lo"), v("lo")), farkasMk([v("k")], [1n])),
          ),
        ),
      ),
    );
    expect(K.checkType(env, term, type).ok).toBe(true);
  });
});
