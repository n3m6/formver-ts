/**
 * Milestone 7, part B: recursive functions.
 *
 * A recursive function is elaborated as a `fixWf` over a tuple of its own parameters, with
 * `B` absorbing the preconditions; a recursive call is an application of the induction
 * hypothesis plus the `pre-call`, `measure-nonneg` and `measure-decrease` proofs.  The tests
 * here check the acceptance case (`examples/pass/sumTo.ts`, whose postcondition needs the
 * callee's postcondition *and* the argument arithmetic), a two-parameter acceptance case,
 * and the failure fixtures with real counterexamples.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import type { Diagnostic, DiagnosticKind } from "../../src/diagnostics";
import * as K from "../../src/kernel/index";
import { verify, type VerifyResult } from "../../src/verify";

const repoRoot = resolve(import.meta.dir, "../..");

function run(relative: string): VerifyResult {
  const path = resolve(repoRoot, relative);
  return verify(path, readFileSync(path, "utf8"));
}

function counterexample(result: VerifyResult, kind: DiagnosticKind): Record<string, string> {
  const found = result.functions
    .flatMap((fn) => fn.obligations)
    .filter((ob) => ob.kind === kind && ob.counterexample !== undefined);
  expect(found.length).toBeGreaterThan(0);
  return found[0]!.counterexample!;
}

describe("recursion: examples/pass/sumTo.ts", () => {
  const result = run("examples/pass/sumTo.ts");

  test("is certified, with every obligation certified and zero axioms", () => {
    expect(result.ok).toBe(true);
    const fn = result.functions[0]!;
    expect(fn.name).toBe("sumTo");
    expect(fn.status).toBe("certified");
    for (const obligation of fn.obligations) {
      expect(`${obligation.siteId}:${obligation.kind}:${obligation.status}`).toBe(
        `${obligation.siteId}:${obligation.kind}:certified`,
      );
    }
    expect(result.axioms).toEqual([]);
    expect(K.axiomsUsed(result.env)).toEqual([]);
  });

  test("the call site owes the preconditions, the measure non-negativity and the decrease", () => {
    const kinds = result.functions[0]!.obligations.map((ob) => ob.kind);
    expect(kinds).toContain("pre-call");
    expect(kinds).toContain("measure-nonneg");
    expect(kinds).toContain("measure-decrease");
  });

  test("the kernel accepted a `fixWf` definition (never a definition that unfolds)", () => {
    const declaration = K.lookupDecl(result.env, "sumTo");
    expect(declaration?.kind).toBe("def");
    if (declaration?.kind !== "def") throw new Error("sumTo is not a definition");
    const text = K.formatTerm(declaration.value);
    expect(text).toContain("fixWf");
    // `fixWf` is opaque: no reduction rule mentions it, so a client can only use the
    // function's type, never unfold it.
    expect(K.lookupPrim("fixWf")?.reduce).toBeUndefined();
  });
});

describe("recursion: a two-parameter acceptance case", () => {
  test("test/e2e/fixtures/recursionCountDown.ts is certified", () => {
    const result = run("test/e2e/fixtures/recursionCountDown.ts");
    expect(result.functions[0]!.status).toBe("certified");
    expect(result.diagnostics).toEqual([]);
    expect(result.axioms).toEqual([]);
  });
});

describe("recursion: failing fixtures", () => {
  test("a measure that does not decrease gives `measure-decrease` at the call", () => {
    const result = run("test/e2e/fixtures/recursionNoDecrease.ts");
    expect(result.ok).toBe(false);
    const reports = result.diagnostics.filter((entry) => entry.kind === "measure-decrease");
    expect(reports.length).toBe(1);
    // The obligation is the recursive call's own site.
    expect(reports[0]!.span.line).toBe(13);
    const fn = result.functions[0]!;
    expect(fn.status).toBe("failed");
    // Every other obligation of the function is certified: the diagnostic is unambiguous.
    for (const obligation of fn.obligations) {
      if (obligation.kind === "measure-decrease") continue;
      expect(`${obligation.kind}:${obligation.status}`).toBe(`${obligation.kind}:certified`);
    }
    // `@decreases lo` and `lo` does not change: no value of `lo` can make `lo < lo` hold.
    const values = counterexample(result, "measure-decrease");
    expect(Object.keys(values).length).toBeGreaterThan(0);
  });

  test("examples/fail/noDecrease.ts gives `error[measure-decrease]` with a counterexample", () => {
    const result = run("examples/fail/noDecrease.ts");
    expect(result.ok).toBe(false);
    const report: Diagnostic | undefined = result.diagnostics.find(
      (entry) => entry.kind === "measure-decrease",
    );
    expect(report).toBeDefined();
    // `spin(n)` calls itself with the same measure: located at the call expression.
    expect(report!.span.file.endsWith("noDecrease.ts")).toBe(true);
    expect(report!.message).toContain("termination measure may not decrease");
    expect(Object.keys(counterexample(result, "measure-decrease")).length).toBeGreaterThan(0);
  });
});
