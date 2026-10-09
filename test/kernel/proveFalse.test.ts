/**
 * Milestone 10: the prove-`false` cases step 7 of `bun run demo` runs.
 *
 * `scripts/prove-false.ts` restates the soundness scenarios of `soundness3.test.ts` so the demo
 * can print the kernel's own rejection reasons without a test runner.  These tests keep the two
 * in sync: every case the demo claims to be rejected must really be rejected, with the reason
 * the demo expects — otherwise the demo would print a false claim about the kernel.
 */
import { describe, expect, test } from "bun:test";
import { proveFalseCases, runProveFalseCase } from "../../scripts/prove-false";

describe("the demo's prove-`false` cases", () => {
  test("there is one case per soundness scenario the demo shows", () => {
    expect(proveFalseCases.length).toBeGreaterThanOrEqual(10);
    expect(new Set(proveFalseCases.map((entry) => entry.name)).size).toBe(proveFalseCases.length);
  });

  for (const entry of proveFalseCases) {
    test(`rejects: ${entry.name}`, () => {
      const outcome = runProveFalseCase(entry);
      expect(outcome.rejection).toBe(entry.expected);
      expect(outcome.rejection).not.toBe("ACCEPTED");
    });
  }
});
