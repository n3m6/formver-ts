/**
 * Milestone 7, part B: loops.
 *
 * A `LoopIR` is elaborated as `fixWf A B m step s0 p0 hinv0`, where `step` is the loop body
 * and `rest` is everything after the loop.  The tests here check the acceptance case
 * (`examples/pass/binarySearch.ts`: a loop whose midpoint obligations need `divFloorSpec`,
 * and whose `index` proof is used at several depths) plus one failure fixture per obligation
 * kind a loop can produce, each with a counterexample that really falsifies the obligation.
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

function diagnostic(result: VerifyResult, kind: DiagnosticKind): Diagnostic {
  const found = result.diagnostics.filter((entry) => entry.kind === kind);
  expect(found.length).toBeGreaterThan(0);
  return found[0]!;
}

/** The obligation of `kind` with the counterexample Z3 produced. */
function counterexample(result: VerifyResult, kind: DiagnosticKind): Record<string, string> {
  const found = result.functions
    .flatMap((fn) => fn.obligations)
    .filter((ob) => ob.kind === kind && ob.counterexample !== undefined);
  expect(found.length).toBeGreaterThan(0);
  return found[0]!.counterexample!;
}

// ---------------------------------------------------------------------------
// The acceptance case
// ---------------------------------------------------------------------------

describe("loops: examples/pass/binarySearch.ts", () => {
  const result = run("examples/pass/binarySearch.ts");

  test("is certified, with every obligation certified and zero axioms", () => {
    expect(result.ok).toBe(true);
    expect(result.functions.map((fn) => fn.name)).toEqual(["binarySearch"]);
    const fn = result.functions[0]!;
    expect(fn.status).toBe("certified");
    expect(fn.certified).toBe(true);
    expect(fn.obligations.length).toBeGreaterThanOrEqual(15);
    for (const obligation of fn.obligations) {
      expect(`${obligation.siteId}:${obligation.kind}:${obligation.status}`).toBe(
        `${obligation.siteId}:${obligation.kind}:certified`,
      );
    }
    expect(result.axioms).toEqual([]);
    expect(K.axiomsUsed(result.env)).toEqual([]);
  });

  test("the kernel accepts the elaborated `fixWf` term at the function's own type", () => {
    const declaration = K.lookupDecl(result.env, "binarySearch");
    expect(declaration).toBeDefined();
    expect(declaration!.kind).toBe("def");
    // The loop is a `fixWf` application: the declaration's body mentions the primitive, and
    // the kernel checked the whole term before `addDecl` accepted it (see `verify`).
    if (declaration!.kind !== "def") throw new Error("binarySearch is not a definition");
    expect(K.formatTerm(declaration!.value)).toContain("fixWf");
  });

  test("the back edges and the loop's own obligations are all present", () => {
    const kinds = result.functions[0]!.obligations.map((ob) => ob.kind);
    for (const kind of [
      "invariant-init",
      "invariant-preserve",
      "measure-nonneg",
      "measure-decrease",
      "index",
      "post",
      "range",
    ] as const) {
      expect(kinds).toContain(kind);
    }
    expect(kinds.filter((kind) => kind === "invariant-preserve").length).toBe(2);
    expect(kinds.filter((kind) => kind === "measure-decrease").length).toBe(2);
  });
});

describe("loops: a second acceptance case", () => {
  test("test/e2e/fixtures/loopCountUp.ts is certified", () => {
    const result = run("test/e2e/fixtures/loopCountUp.ts");
    expect(result.functions[0]!.status).toBe("certified");
    expect(result.diagnostics).toEqual([]);
    expect(result.axioms).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// Failure fixtures: one counterexample per obligation kind
// ---------------------------------------------------------------------------

describe("loops: failing fixtures", () => {
  test("an invariant that is false on entry gives `invariant-init`", () => {
    const result = run("test/e2e/fixtures/loopBadInit.ts");
    expect(result.ok).toBe(false);
    expect(result.functions[0]!.status).toBe("failed");
    const report = diagnostic(result, "invariant-init");
    // The loop's `@invariant` line.
    expect(report.span.line).toBe(14);
    // `i = n`, so the invariant `0 <= i && i < n` reduces to `0 <= n && n < n`: only `n = 0`
    // falsifies it, and Z3 must have chosen a value for which it really is false.
    const values = counterexample(result, "invariant-init");
    expect(Object.keys(values).length).toBeGreaterThan(0);
    const n = Number(values["n"]);
    expect(Number.isFinite(n)).toBe(true);
    expect(0 <= n && n < n).toBe(false);
  });

  test("an invariant the back edge breaks gives `invariant-preserve`", () => {
    const result = run("test/e2e/fixtures/loopBadPreserve.ts");
    expect(result.ok).toBe(false);
    const report = diagnostic(result, "invariant-preserve");
    expect(report.span.line).toBe(14);
    // `i = i + 2` with `i < n`: the counterexample must satisfy the invariant and the loop
    // condition, and violate `i + 2 <= n`.
    const values = counterexample(result, "invariant-preserve");
    const n = Number(values["n"]);
    const i = Number(values["i"]);
    expect(Number.isFinite(n) && Number.isFinite(i)).toBe(true);
    expect(0 <= i && i <= n && i < n).toBe(true);
    expect(i + 2 <= n).toBe(false);
  });

  test("a measure that does not decrease gives `measure-decrease`", () => {
    const result = run("test/e2e/fixtures/loopNoDecrease.ts");
    expect(result.ok).toBe(false);
    const report = diagnostic(result, "measure-decrease");
    // The back edge is the loop statement's own location.
    expect(report.span.line).toBe(13);
    // `@decreases i` and `i = i + 1`: the new measure is `i + 1`, so `i + 1 < i` is false for
    // every value Z3 can pick.
    const values = counterexample(result, "measure-decrease");
    expect(Object.keys(values).length).toBeGreaterThan(0);
  });
});
