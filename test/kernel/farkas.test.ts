/**
 * The Farkas rule: GCD tightening, the certificate arithmetic, and the rejections of
 * specification section 9.1 that apply to milestone 2's literal fragment.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { expectErr, expectOk } from "./helpers";

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

  test("accepts a contradictory literal hypothesis", () => {
    expect(expectOk(K.checkFarkas({ hypTypes: [le(2, 1)], coeffs: [1n] }))).toBeUndefined();
    expect(expectOk(K.checkFarkas({ hypTypes: [le(0, -1)], coeffs: [5n] }))).toBeUndefined();
  });

  test("rejects a satisfiable hypothesis", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [le(2, 2)], coeffs: [1n] })).reason).toBe("farkas-invalid");
    expect(expectErr(K.checkFarkas({ hypTypes: [le(1, 2)], coeffs: [1n] })).reason).toBe("farkas-invalid");
  });

  test("rejects hypotheses that are not `Le`", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [K.Unit], coeffs: [1n] })).reason).toBe(
      "farkas-not-a-le-hypothesis",
    );
    expect(
      expectErr(K.checkFarkas({ hypTypes: [K.Eq(K.Unit, K.tt, K.tt)], coeffs: [1n] })).reason,
    ).toBe("farkas-not-a-le-hypothesis");
  });

  test("rejects a coefficient count mismatch and negative coefficients", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [le(2, 1)], coeffs: [1n, 1n] })).reason).toBe("farkas-shape");
    expect(expectErr(K.checkFarkas({ hypTypes: [le(2, 1), le(2, 1)], coeffs: [1n] })).reason).toBe("farkas-shape");
    expect(expectErr(K.checkFarkas({ hypTypes: [le(2, 1)], coeffs: [-1n] })).reason).toBe(
      "farkas-negative-coefficient",
    );
  });

  test("refuses certificates over atoms, which arrive with the linear normal forms", () => {
    const atomHyp = K.Le(K.varTerm(0), K.intLit(0));
    expect(expectErr(K.checkFarkas({ hypTypes: [atomHyp], coeffs: [1n] })).reason).toBe("farkas-unimplemented");
  });

  test("an empty hypothesis list cannot prove false", () => {
    expect(expectErr(K.checkFarkas({ hypTypes: [], coeffs: [] })).reason).toBe("farkas-invalid");
  });
});
