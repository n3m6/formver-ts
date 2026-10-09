/**
 * Regression (fixc 3), end to end: a verified function may call a **generic** verified
 * function.
 *
 * Section 4.2 accepts "calls to verified functions, in the same file or imported", and
 * section 6.3 gives a generic function the type `(T : Type 0) -> …` — but until now no caller
 * could supply that type argument, so every call to `take`, `safeGet` or `concat` failed with
 * `error[internal] … cannot infer the type argument T`.  The elaborator now infers it from the
 * callee's own parameter types and the call's argument types:
 *
 *   - `readonly number[]` gives `T = Int`;
 *   - a union alias element gives `T = Sum …` (the alias's encoding);
 *   - an argument that is itself a `readonly U[]` parameter gives the *caller's* type
 *     parameter `U` — by position, so caller and callee need not agree on the name.
 *
 * The callers live in an inline source whose path sits in `test/e2e/fixtures/`; the imports
 * are the real `examples/pass` files, read from disk (never imported, never executed).
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { verify, type VerifyResult } from "../../src/verify";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");
const callerPath = resolve(repoRoot, "test/e2e/fixtures/fixc-generic-callers.ts");

/** Verify an inline source as if it were `callerPath`; imports resolve against its directory. */
function run(source: string, options: Parameters<typeof verify>[2] = {}): VerifyResult {
  const readFile = (path: string): string => (path === callerPath ? source : readFileSync(path, "utf8"));
  return verify(callerPath, source, { readFile, ...options });
}

/** Every function certified, no diagnostics, no axioms, no uncertified dependency. */
function expectAllCertified(result: VerifyResult): void {
  expect(result.axioms).toEqual([]);
  expect(result.diagnostics).toEqual([]);
  for (const fn of result.functions) {
    expect(`${fn.name}:${fn.status}`).toBe(`${fn.name}:certified`);
    expect(fn.certified).toBe(true);
    expect(fn.dependsOnUncertified).toEqual([]);
    for (const obligation of fn.obligations) {
      expect(`${fn.name}:${obligation.kind}:${obligation.status}`).toBe(`${fn.name}:${obligation.kind}:certified`);
    }
  }
  expect(result.ok).toBe(true);
}

// ---------------------------------------------------------------------------
// The plan's own generic examples, called from another verified function
// ---------------------------------------------------------------------------

const IMPORTED_CALLERS = `import { take } from "../../../examples/pass/take";
import { safeGet } from "../../../examples/pass/safeGet";
import { concat } from "../../../examples/pass/concat";

/**
 * @pre 0 <= n && n <= a.length
 * @post result.length === n
 */
export function firstN(a: readonly number[], n: number): readonly number[] {
  return take(a, n);
}

/**
 * @pre a.length + b.length <= 4294967295
 * @post result.length === a.length + b.length
 */
export function both(a: readonly number[], b: readonly number[]): readonly number[] {
  return concat(a, b);
}

/**
 * The generic call's result feeds another generic call: take's length is what concat
 * needs, and both type arguments are Int.
 *
 * @pre 0 <= n && n <= a.length
 * @pre a.length + b.length <= 4294967295
 * @post result.length === n + b.length
 */
export function firstNThenRest(a: readonly number[], b: readonly number[], n: number): readonly number[] {
  return concat(take(a, n), b);
}

/**
 * The callee's result type is its own type parameter: firstOf<T> must instantiate safeGet
 * with *its* T, not with Int.
 *
 * @pre 0 <= i && i < a.length
 */
export function firstOf<T>(a: readonly T[], i: number): T {
  return safeGet(a, i);
}
`;

describe("calling the plan's generic examples", () => {
  test("take, safeGet and concat are callable and everything is certified", () => {
    const result = run(IMPORTED_CALLERS);
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
      "firstN:certified",
      "both:certified",
      "firstNThenRest:certified",
      "firstOf:certified",
    ]);
    expectAllCertified(result);
  });

  test("the imported specs are `external` declarations, certified in their own files", () => {
    const result = run(IMPORTED_CALLERS, { verifyImports: true });
    expect(result.externals.map((e) => e.name).sort()).toEqual(["concat", "safeGet", "take"]);
    for (const external of result.externals) expect(external.certified).toBe(true);
    expect(result.ok).toBe(true);
  });

  test("strict mode is happy with a certified caller of a certified generic callee", () => {
    const result = run(IMPORTED_CALLERS, { strict: true, verifyImports: true });
    expect(result.strict).toBe(true);
    expect(result.ok).toBe(true);
    expectAllCertified(result);
  });
});

// ---------------------------------------------------------------------------
// Inference between functions of one file
// ---------------------------------------------------------------------------

const LOCAL_CALLERS = `type U = { readonly kind: "a"; readonly v: number } | { readonly kind: "b"; readonly w: number };

/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function len<T>(a: readonly T[]): number {
  return a.length;
}

/**
 * A number element fixes the type argument at Int.
 *
 * @pre a.length >= 0
 * @post result >= 0
 */
export function numberLen(a: readonly number[]): number {
  return len(a);
}

/**
 * A union alias element fixes it at the alias's Sum encoding.
 *
 * @pre us.length >= 0
 * @post result >= 0
 */
export function unionLen(us: readonly U[]): number {
  return len(us);
}

/**
 * The same callee, but its type parameter has a different name from the caller's.
 *
 * @pre a.length >= 0
 * @post result >= 0
 */
export function lenOf<X>(a: readonly X[]): number {
  return a.length;
}

/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function lenOfNumber(a: readonly number[]): number {
  return lenOf(a);
}

/**
 * @pre 0 <= i && i < a.length
 */
export function getAt<T>(a: readonly T[], i: number): T {
  return a[i];
}

/**
 * A generic caller passing its own type parameter through to a generic callee.
 *
 * @pre 0 <= i && i < a.length
 */
export function echo<T>(a: readonly T[], i: number): T {
  return getAt(a, i);
}
`;

describe("inference between functions of one file", () => {
  test("Int, a union encoding and a caller's type parameter all infer", () => {
    const result = run(LOCAL_CALLERS);
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
      "len:certified",
      "numberLen:certified",
      "unionLen:certified",
      "lenOf:certified",
      "lenOfNumber:certified",
      "getAt:certified",
      "echo:certified",
    ]);
    expectAllCertified(result);
    // The generic functions are kernel `def`s that really quantify over their type parameter.
    for (const name of ["len", "lenOf", "getAt", "echo"]) {
      expect(result.env.decls.get(name)?.kind).toBe("def");
    }
  });

  test("a generic caller of a generic callee is itself callable", () => {
    const result = run(`${LOCAL_CALLERS}
/**
 * @pre 0 <= i && i < a.length
 */
export function echoTwice<T>(a: readonly T[], i: number): T {
  return echo(a, i);
}
`);
    expect(result.ok).toBe(true);
    expect(result.functions.find((fn) => fn.name === "echoTwice")?.status).toBe("certified");
  });

  test("the shape a `TypeIR` cannot read still fails loudly", () => {
    // `bare<T>(x: T)` puts the type parameter outside array-element position, which section
    // 4.2 does not allow (the extractor tolerates it).  There is no `TypeIR` for the vector
    // argument's length in the parameter's own type, so the call cannot be instantiated: the
    // elaborator must fail with an `internal` diagnostic rather than guess `T = Int`.
    const result = run(`${LOCAL_CALLERS}
/** @post result >= 0 */
export function bare<T>(x: T): number {
  return 1;
}

/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function bareCaller(a: readonly number[]): number {
  return bare(a);
}
`);
    expect(result.functions.find((fn) => fn.name === "bare")?.status).toBe("certified");
    expect(result.functions.find((fn) => fn.name === "bareCaller")?.status).toBe("failed");
    expect(result.diagnostics.some((d) => d.kind === "internal" && d.message.includes("cannot infer the type argument"))).toBe(true);
  });
});
