/**
 * Two small contract fixes in the untrusted VC layer, from the independent audit:
 *
 *   1. **The timeout is never silently removed.**  SMT-LIB's `:timeout 0` means "no timeout"
 *      (measured on Z3 5.1.0.0: a 9.7 s instance ran to completion), so a caller that passed
 *      `timeoutMs: 0` used to get an unbounded query.  `0` — and any negative or non-finite
 *      value — now means "the default timeout", and only a positive number is taken
 *      literally.
 *   2. **`sat` alone is invalidity.**  An obligation whose goal mentions no atom (a closed
 *      false proposition) has an empty model, and reporting "Z3 answered sat but produced no
 *      model" as *unknown* hid a real counterexample-less invalidity behind a solver hiccup.
 *      The verdict is `failed` with an empty counterexample.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import * as C from "../../src/vc/certify";
import type { Obligation } from "../../src/vc/obligations";
import * as Z from "../../src/vc/z3";
import { env, span, whenZ3 } from "./helpers";

describe("the per-query timeout", () => {
  test("0, negative and non-finite values mean the default, not `no timeout`", () => {
    expect(Z.effectiveTimeout(undefined)).toBe(Z.DEFAULT_TIMEOUT_MS);
    expect(Z.effectiveTimeout(0)).toBe(Z.DEFAULT_TIMEOUT_MS);
    expect(Z.effectiveTimeout(-1)).toBe(Z.DEFAULT_TIMEOUT_MS);
    expect(Z.effectiveTimeout(Number.NaN)).toBe(Z.DEFAULT_TIMEOUT_MS);
    expect(Z.effectiveTimeout(Number.POSITIVE_INFINITY)).toBe(Z.DEFAULT_TIMEOUT_MS);
  });

  test("a positive timeout is used asis, rounded down to whole milliseconds", () => {
    expect(Z.effectiveTimeout(1)).toBe(1);
    expect(Z.effectiveTimeout(200)).toBe(200);
    expect(Z.effectiveTimeout(12.7)).toBe(12);
  });

  whenZ3("a query with `timeoutMs: 0` still answers (it is bounded, not skipped)", () => {
    const answer = Z.checkSat("(declare-const x Int) (assert (> x 0))", { timeoutMs: 0 });
    expect("status" in answer && answer.status).toBe("sat");
  });

  whenZ3("`certify` accepts `timeoutMs: 0` and finishes", () => {
    // x : Int, h : 0 <= x  |-  0 <= x
    const obligation: Obligation = {
      id: "timeout-zero",
      kind: "post",
      span: span(),
      context: [K.Int, K.Le(K.intLit(0n), K.varTerm(0))],
      hypotheses: [K.Le(K.intLit(0n), K.varTerm(1))],
      proofs: [K.varTerm(0)],
      goal: K.Le(K.intLit(0n), K.varTerm(1)),
      atomNames: {},
    };
    const result = C.certify(env, obligation, { timeoutMs: 0 });
    expect(result.status).toBe("certified");
  });
});

describe("an invalid obligation whose goal mentions no atom", () => {
  whenZ3("is `failed` with an empty counterexample, not `unknown`", () => {
    const obligation: Obligation = {
      id: "closed-false",
      kind: "post",
      span: span(),
      context: [],
      hypotheses: [],
      // `1 <= 0` is false and mentions no atom at all, so Z3's model is empty.
      goal: K.Le(K.intLit(1n), K.intLit(0n)),
      atomNames: {},
    };
    const result = C.certify(env, obligation);
    expect(result.status).toBe("failed");
    expect(result.counterexample).toEqual({});
    expect(result.reason).toContain("does not hold");
    expect(result.reason).not.toContain("no model");
  });
});
