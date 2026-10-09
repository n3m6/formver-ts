/**
 * Regression (fixc 2), end to end: a loop whose `@invariant` (and whose `@post`) contains
 * `===`.
 *
 * Equality enters a loop obligation twice: as a *goal* (the invariant to preserve, an `===`
 * postcondition) and as a *hypothesis* (the invariant the body may assume, which
 * `src/vc/linear.ts` turns into its two `Le` rows by transport).  The transport used to hand
 * `J` a proof of the *reversed* equality, so every obligation whose hypotheses contained the
 * invariant failed with
 *
 *   error[type-mismatch]: expected Eq(Int(), fst ?8, fst (snd ?8)) but got Eq(Int(), fst (snd ?8), fst ?8)
 *
 * reported as a nonsense `measure-decrease: ((n - i) < (n - i)) may not hold`.  The fixture
 * writes `===` in both orientations, in a `while` and in a `for` loop.
 *
 * The differential test is the second half of the check: the certified loop must also be
 * *faithful*.  Swapping the orientation of the goal instead of the proof would make the
 * obligations certify again and disagree with the code, which is exactly what
 * `difftestFile` compares.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { difftestFile } from "../../src/difftest/driver";
import { verify } from "../../src/verify";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");
const fixture = resolve(repoRoot, "test/e2e/fixtures/fixc-loop-eq.ts");

describe("a loop invariant that contains `===`", () => {
  test("every loop obligation is certified, with zero axioms", () => {
    const result = verify(fixture, readFileSync(fixture, "utf8"));
    expect(result.ok).toBe(true);
    expect(result.axioms).toEqual([]);
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
      "countTo:certified",
      "doubleTo:certified",
      "swappedAssertion:certified",
    ]);
    for (const fn of result.functions) {
      expect(fn.dependsOnUncertified).toEqual([]);
      expect(fn.obligations.length).toBeGreaterThan(0);
      for (const obligation of fn.obligations) {
        expect(`${fn.name}#${obligation.siteId}:${obligation.kind}:${obligation.status}`).toBe(
          `${fn.name}#${obligation.siteId}:${obligation.kind}:certified`,
        );
      }
    }
    // The obligation kinds the equality orientation used to break are all exercised.
    const kinds = new Set<string>(result.functions.flatMap((fn) => fn.obligations.map((o) => o.kind)));
    for (const kind of ["invariant-init", "invariant-preserve", "measure-nonneg", "measure-decrease", "post", "range"]) {
      expect(kinds.has(kind)).toBe(true);
    }
    // No diagnostic at all: a nonsense `((n - i) < (n - i)) may not hold` cannot appear.
    expect(result.diagnostics).toEqual([]);
  });

  test("the certified loops are faithful: the interpreter and the original agree", async () => {
    const report = await difftestFile(fixture, { count: 60, seed: 7 });
    expect(report.failures).toEqual([]);
    expect(report.skipped).toEqual([]);
    expect(report.functions.map((fn) => fn.name).sort()).toEqual(["countTo", "doubleTo", "swappedAssertion"]);
  });
});
