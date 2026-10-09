/**
 * Pipeline regressions: the mandate that `verify()` cross-checks every annotated function
 * against `Bun.Transpiler` (section 6.2), and the rule that a file-level `parse` error
 * rejects that file's annotated functions (section 6.5).
 *
 * Both defects were silent.  Nothing imported `src/syntax/crosscheck.ts`, so `verify()`
 * certified functions without ever asking Bun; and a `parse` diagnostic whose span sits
 * outside every function (a truncated file reports the EOF token) left the function
 * `certified`, which a caller then relied on.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { formatDiagnostic, type Diagnostic } from "../../src/diagnostics";
import type * as A from "../../src/syntax/ast";
import { verify } from "../../src/verify";

setDefaultTimeout(60_000);

const repoRoot = resolve(import.meta.dir, "../..");

/** Count `Bun.Transpiler.prototype.transformSync` calls while `body` runs. */
function countTransforms(body: () => void): number {
  const original = Bun.Transpiler.prototype.transformSync;
  let calls = 0;
  Bun.Transpiler.prototype.transformSync = function (
    this: Bun.Transpiler,
    ...args: Parameters<typeof original>
  ) {
    calls += 1;
    return original.apply(this, args);
  } as typeof original;
  try {
    body();
  } finally {
    Bun.Transpiler.prototype.transformSync = original;
  }
  return calls;
}

const TWO_FUNCTIONS = `/** @post result === x */
export function id(x: number): number {
  return x;
}

/** @post result >= 0 */
export function magnitude(x: number): number {
  return x < 0 ? -x : x;
}
`;

function internal(message: string, fn: A.FnDecl): Diagnostic {
  return { kind: "internal", severity: "error", span: fn.span, message };
}

describe("verify() runs the cross-check (section 6.2)", () => {
  test("every annotated function reaches Bun.Transpiler", () => {
    // Two normalisations per function: the original text and our parenthesised printout.
    const calls = countTransforms(() => verify("two.ts", TWO_FUNCTIONS, { solver: false }));
    expect(calls).toBeGreaterThanOrEqual(4);
  });

  test("the transform calls come from the cross-check, not from elsewhere", () => {
    // The control: a cross-check that never asks Bun performs no transformations at all.
    const seen: string[] = [];
    const calls = countTransforms(() => {
      const result = verify("two.ts", TWO_FUNCTIONS, {
        solver: false,
        crosscheck: (fn) => {
          seen.push(fn.name);
          return null;
        },
      });
      expect(result.functions.map((fn) => fn.name)).toEqual(["id", "magnitude"]);
    });
    expect(calls).toBe(0);
    expect(seen).toEqual(["id", "magnitude"]);
  });

  test("the cross-check is consulted for a function the fragment stage rejects too", () => {
    // The mandated order is parse → cross-check → fragment check, so a function that is
    // outside the fragment is still compared with Bun first.
    const source = `/** @post result >= 0 */
export function divided(x: number): number {
  return x / 2;
}
`;
    const seen: string[] = [];
    const result = verify("fragment.ts", source, {
      solver: false,
      crosscheck: (fn) => {
        seen.push(fn.name);
        return null;
      },
    });
    expect(seen).toEqual(["divided"]);
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual(["divided:rejected"]);
    expect(result.diagnostics.some((d) => d.kind === "fragment")).toBe(true);
  });

  test("a cross-check mismatch rejects the function with a located `internal` error", () => {
    const result = verify("mismatch.ts", TWO_FUNCTIONS, {
      solver: false,
      crosscheck: (fn) =>
        fn.name === "id" ? internal(`cross-check failed for \`${fn.name}\``, fn) : null,
    });
    expect(result.ok).toBe(false);
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
      "id:rejected",
      "magnitude:smt-only",
    ]);
    const diagnostic = result.diagnostics.find((d) => d.kind === "internal")!;
    expect(diagnostic).toBeDefined();
    expect(formatDiagnostic(diagnostic)).toContain("cross-check failed for `id`");
    // The mismatch diagnostic keeps the function's own location.
    expect(diagnostic.span.line).toBe(2);
  });

  test("a function with a `parse` error inside its span is not cross-checked", () => {
    const source = `/** @post result === x */
export function good(x: number): number {
  return x;
}

/** @post result === x */
export function bad(x: number): number {
  return x +;
}
`;
    const seen: string[] = [];
    const calls = countTransforms(() => {
      const result = verify("parse.ts", source, {
        solver: false,
        crosscheck: (fn) => {
          seen.push(fn.name);
          return null;
        },
      });
      expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
        "good:smt-only",
        "bad:rejected",
      ]);
      expect(result.diagnostics.some((d) => d.kind === "parse")).toBe(true);
    });
    expect(seen).toEqual(["good"]);
    expect(calls).toBe(0);
  });

  test("the real cross-check agrees with Bun on `examples/pass/clamp.ts`", () => {
    const source = `/** @pre lo <= hi
 * @post lo <= result && result <= hi */
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
`;
    const result = verify("clamp.ts", source, { solver: false });
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
    expect(result.functions[0]!.status).not.toBe("rejected");
  });
});

describe("a file-level `parse` error rejects every annotated function", () => {
  const TRUNCATED = `/** @post result === x */
export function good(x: number): number {
  if (x < 0) return -x;
  return x;
}

/** @post result === x */
export function cut(x: number): number {
`;

  test("a truncated body reported at EOF does not leave a function certified", () => {
    const result = verify("/tmp/fixb-e2e/broken.ts", TRUNCATED, { solver: false });
    expect(result.ok).toBe(false);
    expect(result.functions.length).toBe(2);
    for (const verdict of result.functions) {
      expect(`${verdict.name}:${verdict.status}`).toBe(`${verdict.name}:rejected`);
      expect(verdict.certified).toBe(false);
    }
    expect(result.diagnostics.some((d) => d.kind === "parse")).toBe(true);
  });

  test("a caller cannot rely on a function from such a file", () => {
    // Real files: `resolveImportPath` resolves an import against the filesystem.
    const dir = join(repoRoot, ".dep-verify", `fixb-parse-${process.pid}-${Date.now()}`);
    mkdirSync(dir, { recursive: true });
    const brokenPath = join(dir, "broken.ts");
    const callerPath = join(dir, "caller.ts");
    const caller = `import { good } from "./broken";

/** @post 0 <= result */
export function use(x: number): number {
  return good(x);
}
`;
    writeFileSync(brokenPath, TRUNCATED, "utf8");
    writeFileSync(callerPath, caller, "utf8");
    try {
      const result = verify(callerPath, caller, { verifyImports: true, strict: true, solver: false });
      expect(result.externals[0]!.certified).toBe(false);
      expect(result.functions[0]!.dependsOnUncertified).toContain("good");
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  test("a `parse` error inside one function still rejects only that function", () => {
    const source = `/** @post result === x */
export function good(x: number): number {
  return x;
}

/** @post result === x */
export function bad(x: number): number {
  return x +;
}
`;
    const result = verify("/tmp/fixb-e2e/inline.ts", source, { solver: false });
    expect(result.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual([
      "good:smt-only",
      "bad:rejected",
    ]);
  });
});
