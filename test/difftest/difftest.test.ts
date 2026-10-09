/**
 * The acceptance path of milestone 9 (specification 6.8 and 9.4): the differential test for
 * **every function in `examples/pass`, 200 inputs each**.
 *
 * Each test here reads a report the `beforeAll` computed once per file: the run itself is
 * slow (it verifies the file, imports it through the plugin, and interprets 200 inputs), so
 * the assertions share one run.
 */
import { beforeAll, describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { extractFile } from "../../src/extract/fragment";
import { difftestFile, failingPostconditions, formatDifftestReport, type DifftestReport } from "../../src/difftest/driver";

// Verifying `binarySearch` and interpreting 200 inputs through its loop takes seconds.
setDefaultTimeout(300_000);

const repoRoot = resolve(import.meta.dir, "../..");

const PASS_FILES = [
  "examples/pass/clamp.ts",
  "examples/pass/abs.ts",
  "examples/pass/safeGet.ts",
  "examples/pass/concat.ts",
  "examples/pass/take.ts",
  "examples/pass/shape.ts",
  "examples/pass/useClamp.ts",
  "examples/pass/binarySearch.ts",
  "examples/pass/sumTo.ts",
] as const;

/** Every function of `examples/pass`, with the file it lives in. */
const PASS_FUNCTIONS: readonly [string, string][] = [
  ["examples/pass/clamp.ts", "clamp"],
  ["examples/pass/abs.ts", "abs"],
  ["examples/pass/safeGet.ts", "safeGet"],
  ["examples/pass/concat.ts", "concat"],
  ["examples/pass/take.ts", "take"],
  ["examples/pass/shape.ts", "perimeter"],
  ["examples/pass/useClamp.ts", "percent"],
  ["examples/pass/binarySearch.ts", "binarySearch"],
  ["examples/pass/sumTo.ts", "sumTo"],
];

const reports = new Map<string, DifftestReport>();

beforeAll(async () => {
  for (const file of PASS_FILES) {
    reports.set(file, await difftestFile(resolve(repoRoot, file), { count: 200 }));
  }
});

function reportOf(file: string): DifftestReport {
  const report = reports.get(file);
  if (report === undefined) throw new Error(`no difftest report for ${file}`);
  return report;
}

describe("differential test: examples/pass, 200 inputs per function", () => {
  for (const file of PASS_FILES) {
    test(`${file}: the original and the interpreter agree, and every @post holds`, () => {
      const report = reportOf(file);
      // The full diagnostic, so a failure is readable from the test output.
      if (!report.ok) throw new Error(formatDifftestReport(report));
      expect(report.failures).toEqual([]);
      expect(report.skipped).toEqual([]);
      expect(report.functions.length).toBe(1);
      const fn = report.functions[0]!;
      expect(fn.cases).toBe(200);
      expect(fn.givenUp).toBe(0);
    });
  }

  test("every function of every passing example is covered", () => {
    const covered = new Set<string>();
    for (const report of reports.values()) for (const fn of report.functions) covered.add(fn.name);
    expect([...covered].sort()).toEqual(PASS_FUNCTIONS.map(([, name]) => name).sort());
  });

  test("loops and recursion are exercised (binarySearch, sumTo)", () => {
    const search = reportOf("examples/pass/binarySearch.ts").functions[0]!;
    const sum = reportOf("examples/pass/sumTo.ts").functions[0]!;
    expect(search.cases).toBe(200);
    expect(sum.cases).toBe(200);
    // `sumTo`'s `@pre` caps `n`, so the recursive calls terminate; the generator's rejection
    // loop is visible in its attempt count.
    expect(sum.attempts).toBeGreaterThanOrEqual(200);
  });

  test("a report has one line per function and names the file", () => {
    const text = formatDifftestReport(reportOf("examples/pass/clamp.ts"));
    expect(text).toContain("examples/pass/clamp.ts");
    expect(text).toContain("clamp: 200 input(s)");
    expect(text).toContain("ok");
  });
});

describe("the injected runtime checks are active during the difftest", () => {
  test("a precondition violation throws the injected PreconditionError", async () => {
    const module = (await import("../../examples/pass/clamp")) as typeof import("../../examples/pass/clamp");
    // `lo <= hi` is `clamp`'s precondition; the plugin injected the check at its entry.
    expect(() => module.clamp(5, 2, 1)).toThrow(/precondition/);
  });

  test("the loop's decrease monitor is per call, so a second call is not a false alarm", async () => {
    const module = (await import("../../examples/pass/binarySearch")) as typeof import("../../examples/pass/binarySearch");
    // The monitor keeps state per source location; without the entry reset the second call
    // of the same function would compare against the first call's final measure.
    const first = module.binarySearch([1, 3, 5, 7], 5);
    const second = module.binarySearch([1, 3, 5, 7], 5);
    expect(first).toBe(2);
    expect(second).toBe(2);
  });
});

describe("@post evaluation", () => {
  test("a satisfied postcondition reports nothing; a violated one reports its text", () => {
    const path = resolve(repoRoot, "examples/pass/sumTo.ts");
    const fn = extractFile(path, readFileSync(path, "utf8")).functions[0]!;
    // `sumTo(3)` is 6, and the post is `0 <= result && result <= n * 1000000`.
    expect(failingPostconditions(fn, [3], 6)).toEqual([]);
    const violated = failingPostconditions(fn, [3], -1);
    expect(violated).toHaveLength(1);
    expect(violated[0]!.spec).toContain("0 <= result");
    // A result the spec cannot read (no `result` at all) is a failure, not a pass.
    expect(failingPostconditions(fn, [3], undefined)).toHaveLength(1);
  });

  test("a vector result's postcondition reads its length", () => {
    const path = resolve(repoRoot, "examples/pass/take.ts");
    const fn = extractFile(path, readFileSync(path, "utf8")).functions[0]!;
    // `@post result.length === n`.
    expect(failingPostconditions(fn, [[9, 8, 7], 2], [9, 8])).toEqual([]);
    expect(failingPostconditions(fn, [[9, 8, 7], 2], [9])).toHaveLength(1);
  });
});
