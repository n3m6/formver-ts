/**
 * Tests for the input generator and the spec evaluator (milestone 9).
 *
 * The generator is seeded, so these tests are deterministic; the `@pre` filter is the one
 * evaluator of spec expressions, and it is exercised on real extracted functions rather than
 * on hand-written predicates.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import {
  extractFile,
  type Binder,
  type ExprIR,
  type FunctionIR,
  type TypeIR,
} from "../../src/extract/fragment";
import * as K from "../../src/kernel/index";
import {
  DEFAULT_MAX_ATTEMPTS,
  EDGE_INTS,
  Rng,
  evaluateSpec,
  generateCandidate,
  generateInputs,
  makeRng,
  preconditionsHold,
  specEnvFor,
  type InputValue,
} from "../../src/difftest/gen";

const repoRoot = resolve(import.meta.dir, "../..");

/** The `FunctionIR` of the only function of an example file. */
function exampleFn(relative: string): FunctionIR {
  const path = resolve(repoRoot, relative);
  const ir = extractFile(path, readFileSync(path, "utf8"));
  expect(ir.diagnostics.filter((d) => d.severity === "error")).toEqual([]);
  return ir.functions[0]!;
}

/** The `FunctionIR` of a function written for one test. */
function sourceFn(source: string): FunctionIR {
  const ir = extractFile(resolve(repoRoot, "test/difftest/fixture.ts"), source);
  expect(ir.diagnostics.filter((d) => d.severity === "error")).toEqual([]);
  return ir.functions[0]!;
}

describe("the PRNG", () => {
  test("is deterministic in the seed", () => {
    const a = new Rng(7);
    const b = new Rng(7);
    const c = new Rng(8);
    const streamA = [a.nextBits(), a.nextBits(), a.nextBits()];
    expect([b.nextBits(), b.nextBits(), b.nextBits()]).toEqual(streamA);
    expect([c.nextBits(), c.nextBits(), c.nextBits()]).not.toEqual(streamA);
  });

  test("int() stays in range and pick() returns an element", () => {
    const rng = makeRng(3);
    for (let i = 0; i < 100; i += 1) {
      const value = rng.int(-5, 6);
      expect(value).toBeGreaterThanOrEqual(-5);
      expect(value).toBeLessThan(6);
      expect([10, 20]).toContain(rng.pick([10, 20]));
    }
  });
});

describe("input generation", () => {
  test("the same seed gives the same inputs; a different seed usually gives others", () => {
    const fn = exampleFn("examples/pass/clamp.ts");
    const first = generateInputs(fn, { seed: 42, count: 25 });
    const again = generateInputs(fn, { seed: 42, count: 25 });
    expect(again.inputs).toEqual(first.inputs);
    expect(again.attempts).toBe(first.attempts);
    const other = generateInputs(fn, { seed: 43, count: 25 });
    expect(other.inputs).not.toEqual(first.inputs);
  });

  test("edge values appear where `@pre` allows them", () => {
    // `abs` has no precondition, so every edge value is a legal input.
    const fn = exampleFn("examples/pass/abs.ts");
    const generated = generateInputs(fn, { seed: 1, count: 200 });
    const seen = new Set(generated.inputs.map((values) => BigInt(values[0] as number)));
    for (const edge of EDGE_INTS) expect(seen.has(edge)).toBe(true);
    // ... and the uniform range is used too.
    expect(generated.inputs.some((values) => Math.abs(values[0] as number) > 100)).toBe(true);
  });

  test("arrays have length 0 to 8 and their `number` elements are integers", () => {
    const fn = exampleFn("examples/pass/concat.ts");
    const generated = generateInputs(fn, { seed: 5, count: 100 });
    for (const values of generated.inputs) {
      for (const value of values as readonly (readonly number[])[]) {
        expect(value.length).toBeLessThanOrEqual(8);
        for (const element of value) expect(Number.isSafeInteger(element)).toBe(true);
      }
    }
    expect(generated.inputs.some((values) => (values[0] as readonly number[]).length === 0)).toBe(true);
    expect(generated.inputs.some((values) => (values[0] as readonly number[]).length === 8)).toBe(true);
  });

  test("union inputs are a real variant with `number` fields", () => {
    const fn = exampleFn("examples/pass/shape.ts");
    const generated = generateInputs(fn, { seed: 9, count: 100 });
    const tags = new Set<string>();
    for (const values of generated.inputs) {
      const shape = values[0] as Record<string, InputValue>;
      tags.add(String(shape.kind));
      if (shape.kind === "square") expect(Number.isSafeInteger(shape.side)).toBe(true);
      else expect(Number.isSafeInteger(shape.w) && Number.isSafeInteger(shape.h)).toBe(true);
    }
    expect([...tags].sort()).toEqual(["rect", "square"]);
  });

  test("inputs that violate `@pre` are rejected, not used", () => {
    // `sumTo` requires `0 <= n <= 1000000`; the generator proposes ±(2^53-1) as well.
    const fn = exampleFn("examples/pass/sumTo.ts");
    const generated = generateInputs(fn, { seed: 11, count: 100 });
    expect(generated.rejected).toBeGreaterThan(0);
    for (const values of generated.inputs) {
      const n = values[0] as number;
      expect(n).toBeGreaterThanOrEqual(0);
      expect(n).toBeLessThanOrEqual(1_000_000);
    }
    // `safeGet` additionally needs an index inside the array it got.
    const safeGet = exampleFn("examples/pass/safeGet.ts");
    for (const values of generateInputs(safeGet, { seed: 12, count: 50 }).inputs) {
      const [array, index] = values as readonly [readonly number[], number];
      expect(index).toBeGreaterThanOrEqual(0);
      expect(index).toBeLessThan(array.length);
    }
  });

  test("an unsatisfiable `@pre` gives up after the bounded number of attempts", () => {
    const fn = sourceFn(`
      /**
       * @pre n >= 0
       * @pre n <= -1
       */
      export function never(n: number): number { return n; }
    `);
    const generated = generateInputs(fn, { count: 5, maxAttempts: 3 });
    expect(generated.inputs).toEqual([]);
    expect(generated.givenUp).toBe(5);
    expect(generated.attempts).toBe(15);
    expect(generated.rejected).toBe(15);
    expect(DEFAULT_MAX_ATTEMPTS).toBeGreaterThan(3);
  });

  test("a candidate is a value per parameter, and `preconditionsHold` agrees", () => {
    const fn = exampleFn("examples/pass/clamp.ts");
    const candidate = generateCandidate(fn, makeRng(2));
    expect(candidate).toHaveLength(3);
    for (const value of candidate) expect(typeof value).toBe("number");
    expect(preconditionsHold(fn, candidate)).toBe(typeof candidate[0] === "number" && candidate[1]! <= candidate[2]!);
  });
});

describe("spec evaluation over JS values", () => {
  test("arithmetic, comparisons and `length` on parameters and `result`", () => {
    const fn = sourceFn(`
      /**
       * @pre a.length >= 1
       * @pre 0 <= i && i < a.length
       * @post result === i + a.length
       */
      export function pick(a: readonly number[], i: number): number {
        return a[0];
      }
    `);
    const pre0 = fn.signature.preconditions[0]!.prop;
    const pre1 = fn.signature.preconditions[1]!.prop;
    const post = fn.signature.result.posts[0]!.prop;

    expect(evaluateSpec(pre0, specEnvFor(fn, [[5, 6], 1]))).toBe(true);
    expect(evaluateSpec(pre0, specEnvFor(fn, [[], 0]))).toBe(false);
    expect(evaluateSpec(pre1, specEnvFor(fn, [[5, 6], 2]))).toBe(false);
    expect(evaluateSpec(pre1, specEnvFor(fn, [[5, 6], 1]))).toBe(true);
    // The `@post` reads `result` (`i + a.length` is `1 + 2 = 3` here).
    expect(evaluateSpec(post, specEnvFor(fn, [[5, 6], 1], 3))).toBe(true);
    expect(evaluateSpec(post, specEnvFor(fn, [[5, 6], 1], 4))).toBe(false);
    // `result.length` is the JS array's length (this is the layout `take`/`concat` use).
    const take = exampleFn("examples/pass/take.ts");
    const takePost = take.signature.result.posts[0]!.prop;
    expect(evaluateSpec(takePost, specEnvFor(take, [[1, 2, 3], 2], [1, 2]))).toBe(true);
    expect(evaluateSpec(takePost, specEnvFor(take, [[1, 2, 3], 2], [1]))).toBe(false);
  });

  test("a ternary condition is evaluated on the branch it takes", () => {
    const fn = exampleFn("examples/pass/shape.ts");
    const pre = fn.signature.preconditions[0]!.prop;
    expect(evaluateSpec(pre, specEnvFor(fn, [{ kind: "square", side: 3 }]))).toBe(true);
    expect(evaluateSpec(pre, specEnvFor(fn, [{ kind: "square", side: -3 }]))).toBe(false);
    expect(evaluateSpec(pre, specEnvFor(fn, [{ kind: "rect", w: 3, h: 4 }]))).toBe(true);
    expect(evaluateSpec(pre, specEnvFor(fn, [{ kind: "rect", w: 3, h: 2_000_000 }]))).toBe(false);
  });

  test("the prelude calls in a spec are Math.max/min/abs and floor/trunc division", () => {
    const fn = sourceFn(`
      /**
       * @pre Math.abs(n) <= 100
       * @post result >= n
       */
      export function magnitude(n: number): number {
        return Math.max(n, Math.abs(n));
      }
    `);
    const pre = fn.signature.preconditions[0]!.prop;
    expect(evaluateSpec(pre, specEnvFor(fn, [-50]))).toBe(true);
    expect(evaluateSpec(pre, specEnvFor(fn, [-101]))).toBe(false);
    const post = fn.signature.result.posts[0]!.prop;
    expect(evaluateSpec(post, specEnvFor(fn, [-50], 50))).toBe(true);
    expect(evaluateSpec(post, specEnvFor(fn, [-50], -51))).toBe(false);
  });

  test("an array element read in a spec is the JS element at that index", () => {
    // The examples never read array elements in a spec (elements are opaque), but the
    // evaluator handles `a[i]` because the extractor's grammar has it.
    const fn = sourceFn(
      "/** @post result > 0 */ export function first(a: readonly number[]): number { return a[0]; }",
    );
    const span = { file: "x.ts", line: 1, col: 1, offset: 0 };
    const intType: TypeIR = { kind: "int", span };
    const param = fn.params[0]!;
    const ref: ExprIR = {
      kind: "ref",
      span,
      type: param.type,
      args: [],
      slot: { kind: "binder", binder: param.binder },
      sites: [],
      facts: [],
    };
    const index: ExprIR = {
      kind: "index",
      span,
      type: intType,
      args: [ref, { kind: "int", span, type: intType, args: [], literal: 1n, sites: [], facts: [] }],
      siteId: 1,
      sites: [],
      facts: [],
    };
    // The element comes back as the JS value it is; comparisons normalise it.
    expect(evaluateSpec(index, specEnvFor(fn, [[7, 8]]))).toBe(8);
    expect(evaluateSpec(index, specEnvFor(fn, [[]]))).toBeUndefined();
  });

  test("a spec with no value for a variable is not evaluable, so it does not hold", () => {
    const fn = sourceFn(`
      /**
       * @pre n > 0
       * @post result >= 0
       */
      export function positive(n: number): number { return n; }
    `);
    const pre = fn.signature.preconditions[0]!.prop;
    // A missing binder value is not evaluable.
    expect(evaluateSpec(pre, specEnvFor(fn, []))).toBeUndefined();
    expect(preconditionsHold(fn, [])).toBe(false);
  });
});
