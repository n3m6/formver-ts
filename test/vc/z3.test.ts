/**
 * The `bun:ffi` Z3 binding (specification 6.4): availability without a hard failure,
 * push/pop isolation, error detection with a context reset, and the per-query timeout.
 */
import { describe, expect, test } from "bun:test";
import * as Z from "../../src/vc/z3";
import { whenZ3, z3Available } from "./helpers";

describe("availability", () => {
  test("reports availability instead of throwing when the library is missing", () => {
    // Both branches are fine: the point is that neither `isAvailable` nor
    // `unavailableReason` throws at import time or at call time.
    if (z3Available) {
      expect(Z.isAvailable()).toBe(true);
      expect(Z.unavailableReason()).toBeUndefined();
      expect(Z.libraryPath().length).toBeGreaterThan(0);
    } else {
      expect(Z.isAvailable()).toBe(false);
      expect(Z.unavailableReason()).toContain("libz3");
    }
  });
});

describe("queries", () => {
  whenZ3("loads the pinned release and reports its version", () => {
    expect(Z.version()).toContain("Z3");
    expect(Z.version()).toContain("5.1.0");
  });

  whenZ3("answers a query and keeps declarations local to it", () => {
    const first = Z.checkSat("(declare-const x Int) (assert (> x 2))");
    expect(first).toMatchObject({ status: "sat" });
    // The `(push)`/`(pop)` wrapper must drop the declaration: re-declaring it is fine.
    const second = Z.evalScript("(declare-const x Int) (assert (= x 1))");
    expect(second.ok).toBe(true);
    expect(second.output).toBe("");
    const model = Z.evalScript("(declare-const x Int) (assert (= x 7)) (check-sat) (get-model)");
    expect(model.output).toContain("(define-fun x () Int");
  });

  whenZ3("reports `unknown` as a verdict, not as an error", () => {
    // Pigeonhole: 13 pigeons in 12 holes is unsat but takes Z3 about 10 seconds.
    const pigeons = pigeonholeScript();
    const answer = Z.checkSat(pigeons, { timeoutMs: 200 });
    expect("status" in answer && answer.status).toBe("unknown");
  });

  whenZ3("rejects a malformed script and recovers by recreating the context", () => {
    const epochBefore = Z.contextEpoch();
    const broken = Z.evalScript("(declare-const q Int) (assert (= q 1) (check-sat)");
    expect(broken.ok).toBe(false);
    expect(broken.error).toContain("Z3 rejected the query");
    expect(broken.output).toContain("(error");
    // An error means the state may be unbalanced: the context is recreated.
    expect(Z.contextEpoch()).toBeGreaterThan(epochBefore);
    // ... and the next query still works.
    const after = Z.checkSat("(declare-const q Int) (assert (= q 1))");
    expect(after).toMatchObject({ status: "sat" });
  });

  whenZ3("treats an unknown command as a failure", () => {
    const reply = Z.evalScript("(frobnicate 1)");
    expect(reply.ok).toBe(false);
    expect(reply.error).toContain("does not support");
    expect(Z.checkSat("(declare-const ok Int) (assert (= ok 3))")).toMatchObject({ status: "sat" });
  });

  whenZ3("never mistakes a model for a verdict", () => {
    const reply = Z.evalScript("(declare-const a Int) (assert (> a 4)) (check-sat) (get-model)");
    expect(reply.ok).toBe(true);
    expect(reply.output.split("\n")[0]!.trim()).toBe("sat");
  });
});

/** 13 pigeons, 12 holes, one pigeon per hole: unsat, and slow without a timeout. */
export function pigeonholeScript(pigeons = 13, holes = 12): string {
  const lines: string[] = [];
  for (let pigeon = 0; pigeon < pigeons; pigeon += 1) {
    lines.push(`(declare-const p${pigeon} Int)`, `(assert (>= p${pigeon} 0))`, `(assert (< p${pigeon} ${holes}))`);
  }
  for (let hole = 0; hole < holes; hole += 1) {
    const indicators = Array.from({ length: pigeons }, (_, pigeon) => `(ite (= p${pigeon} ${hole}) 1 0)`);
    lines.push(`(assert (<= (+ ${indicators.join(" ")}) 1))`);
  }
  return lines.join("\n");
}
