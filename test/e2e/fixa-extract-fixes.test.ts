/**
 * End-to-end regression tests for the three extraction defects (a companion to
 * `test/extract/fixa.test.ts`, which checks the diagnostics and the IR).
 *
 * Each case goes through the whole pipeline (`verify` → elaborate → certify → kernel), so a
 * verdict of `certified` here means the elaborated term agrees with the JavaScript.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { resolve } from "node:path";
import { verify, type VerifyResult } from "../../src/verify";

// The canonical `for` loop's obligations go through Z3; the 5 s default is too tight.
setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");

function run(name: string, source: string): VerifyResult {
  return verify(resolve(repoRoot, `examples/pass/fixa-${name}.ts`), source);
}

function statuses(result: VerifyResult): string[] {
  return result.functions.map((fn) => `${fn.name}:${fn.status}`);
}

function locatedFragment(result: VerifyResult, needle: string) {
  const found = result.diagnostics.filter((d) => d.kind === "fragment" && d.message.includes(needle));
  expect(found).toHaveLength(1);
  const diagnostic = found[0]!;
  expect(diagnostic.severity).toBe("error");
  expect(diagnostic.span.line).toBeGreaterThan(0);
  expect(diagnostic.span.col).toBeGreaterThan(0);
  expect(diagnostic.span.offset).toBeGreaterThan(0);
  return diagnostic;
}

// ---------------------------------------------------------------------------
// 1. a statement-level block must not leak its bindings
// ---------------------------------------------------------------------------

describe("1. a bare block is rejected, not elaborated", () => {
  test("a block shadowing a parameter is not certified", () => {
    const result = run(
      "shadowParam",
      `/**
 * @pre x >= 0 && x <= 100
 * @post result === 5
 */
export function f(x: number): number {
  {
    let x = 5;
  }
  return x;
}
`,
    );
    expect(result.ok).toBe(false);
    expect(statuses(result)).toEqual(["f:rejected"]);
    const diagnostic = locatedFragment(result, "block statement is not allowed");
    expect(diagnostic.span.line).toBe(6);
    // Nothing was elaborated for it, so the function carries no obligations.
    expect(result.functions[0]!.obligations).toEqual([]);
  });

  test("a binding declared in a block does not survive it", () => {
    const result = run(
      "shadowLet",
      `/**
 * @pre x >= 0
 * @post result === 5
 */
export function f(x: number): number {
  {
    let y = 5;
  }
  return y;
}
`,
    );
    expect(result.ok).toBe(false);
    expect(statuses(result)).toEqual(["f:rejected"]);
    locatedFragment(result, "block statement is not allowed");
  });

  test("a block inside an `if` body still works", () => {
    const result = run(
      "blockInIf",
      `/**
 * @pre -100 <= x && x <= 100
 * @post result >= 0
 */
export function f(x: number): number {
  if (x > 0) {
    const z = 1;
    return z;
  }
  return 0;
}
`,
    );
    expect(result.diagnostics).toEqual([]);
    expect(statuses(result)).toEqual(["f:certified"]);
  });
});

// ---------------------------------------------------------------------------
// 2. call-site argument types
// ---------------------------------------------------------------------------

describe("2. a wrong-typed argument is a located `fragment` error", () => {
  const callee = `/**
 * @pre x >= 0
 * @post result >= 0
 */
export function g(x: number): number {
  return x;
}
`;

  test("`readonly number[]` passed to a `number` parameter", () => {
    const result = run(
      "arrayArg",
      `${callee}/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function f(a: readonly number[]): number {
  return g(a);
}
`,
    );
    expect(result.ok).toBe(false);
    expect(statuses(result)).toEqual(["g:certified", "f:rejected"]);
    const diagnostic = locatedFragment(result, "`g` needs `number` for the parameter `x`");
    expect(diagnostic.message).toContain("`a` has type `readonly number[]`");
    // The argument on line 13, not the call, the callee or the file.
    expect(diagnostic.span.line).toBe(13);
    // No `internal` diagnostic: the failure is understood by the fragment checker.
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
  });

  test("a union value passed to a `number` parameter", () => {
    const result = run(
      "unionArg",
      `type U = { readonly kind: "a"; readonly v: number } | { readonly kind: "b"; readonly w: number };
${callee}/**
 * @pre u.kind === "a"
 * @post result >= 0
 */
export function f(u: U): number {
  return g(u);
}
`,
    );
    expect(result.ok).toBe(false);
    const diagnostic = locatedFragment(result, "`g` needs `number` for the parameter `x`");
    expect(diagnostic.message).toContain("has type `U`");
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// 3. `for (let i = e; c; update)`
// ---------------------------------------------------------------------------

describe("3. the canonical `for` loop verifies", () => {
  const canonical = `/**
 * @pre 0 <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number): number {
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = 0; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;

  test("`for (let i = 0; i < n; i = i + 1)` is kernel-certified", () => {
    const result = run("forCanonical", canonical);
    expect(result.diagnostics).toEqual([]);
    expect(statuses(result)).toEqual(["f:certified"]);
    expect(result.functions[0]!.certified).toBe(true);
    expect(result.axioms).toEqual([]);
    // The loop's own obligations are all present and certified.
    const kinds = result.functions[0]!.obligations.map((ob) => ob.kind);
    for (const kind of [
      "invariant-init",
      "invariant-preserve",
      "measure-nonneg",
      "measure-decrease",
      "range",
      "post",
    ] as const) {
      expect(kinds).toContain(kind);
    }
    for (const obligation of result.functions[0]!.obligations) {
      expect(`${obligation.siteId}:${obligation.kind}:${obligation.status}`).toBe(
        `${obligation.siteId}:${obligation.kind}:certified`,
      );
    }
    // The mandated update `i = i + 1` is inside the safe range because the invariant bounds
    // `i`: the obligation for it exists, is certified and has no counterexample.
    const update = result.functions[0]!.obligations.find(
      (ob) => ob.kind === "range" && ob.text.includes("(i + 1)"),
    );
    expect(update).toBeDefined();
    expect(update!.status).toBe("certified");
    expect(update!.counterexample).toBeUndefined();
  });

  test("the `i++` spelling of the update is certified as well", () => {
    const result = run("forCanonicalPlusPlus", canonical.replace("i = i + 1", "i++"));
    expect(result.diagnostics).toEqual([]);
    expect(statuses(result)).toEqual(["f:certified"]);
  });

  test("`@decreases`/`@invariant` may mention the loop variable without `unresolved name`", () => {
    // Before the fix the loop's spec was re-checked in the enclosing environment, where the
    // `for`'s own `let i` does not exist.
    const result = run(
      "forMeasureI",
      `/**
 * @pre 0 <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number): number {
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = 0; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`,
    );
    expect(result.diagnostics.filter((d) => d.message.includes("unresolved name `i`"))).toEqual([]);
  });

  test("a counter initialized by a call is one located `fragment` error, not `internal`", () => {
    const result = run(
      "forCallInit",
      `/**
 * @pre 0 <= x && x <= 10
 * @post result === x
 */
export function start(x: number): number {
  return x;
}
/**
 * @pre 0 <= x && x <= 10 && x <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number, x: number): number {
  let acc = 0;
  /**
   * @invariant x <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = start(x); i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`,
    );
    expect(result.ok).toBe(false);
    expect(statuses(result)).toEqual(["start:certified", "f:rejected"]);
    locatedFragment(result, "cannot be initialized by an expression whose term needs an obligation proof");
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
  });

  test("reading the loop variable after the loop is rejected", () => {
    const result = run("forCounterAfter", canonical.replace("  return acc;", "  return i;"));
    expect(result.ok).toBe(false);
    expect(statuses(result)).toEqual(["f:rejected"]);
    // `ReferenceError` in JavaScript; a located `fragment` error here.
    locatedFragment(result, "unresolved name `i`");
  });
});
