/**
 * Tests for the hygiene checker itself (`test/hygiene.test.ts`).
 *
 * A checker that cannot catch an evasion is worse than none, so these cases are the ones a
 * previous revision missed: computed dynamic imports, aliased `require`, `globalThis` reached
 * through an alias, globals hidden in template interpolations — plus the false positives
 * (imports mentioned inside strings or template literals) that must NOT be reported.
 */
import { describe, expect, test } from "bun:test";
import { dynamicModuleReferences, hygieneViolations, importSpecifiers, stripSource } from "./hygiene.test";

describe("hygiene checker", () => {
  test("flags the evasions the previous regex checker missed", () => {
    const cases: ReadonlyArray<readonly [string, string]> = [
      ["computed dynamic import", 'const name = "bun" + ":ffi"; export const f = () => import(name);'],
      ["template dynamic import", "export const f = () => import(`bun:${'ffi'}`);"],
      ["concatenated dynamic import", 'export const f = () => import("bun:" + "ffi");'],
      ["aliased require", 'const r = require; export const f = () => r("bun:ffi");'],
      ["bare require", 'export const f = () => require("bun:ffi");'],
      ["aliased globalThis", 'const g: any = globalThis; export const v = () => g.Bun.version;'],
      ["bracket globalThis", 'export const v = () => globalThis["Bun"].version;'],
      ["optional-chained globalThis", 'export const v = () => globalThis?.Bun.version;'],
      ["globalThis in a template interpolation", "export const v = `${globalThis.Bun.version}`;"],
      ["process", "export const v = process.env.HOME;"],
      ["console", "export function log(x: number): void { console.log(x); }"],
      ["import.meta", "export const v = import.meta.dir;"],
      ["eval", "export const v = eval('1');"],
      ["Buffer", "export const v = Buffer.from('x');"],
    ];
    for (const [what, source] of cases) {
      expect(`${what}: ${hygieneViolations(source).length > 0 ? "flagged" : "MISSED"}`).toBe(`${what}: flagged`);
    }
  });

  test("does not flag a clean kernel-shaped source", () => {
    const clean = [
      'import { evalTerm } from "./eval";',
      'import type { Term } from "./term";',
      "export function id(term: Term): Term {",
      "  // Bun is not used here, and neither is globalThis",
      '  const note = "import { x } from \\"bun:ffi\\" is never used in the kernel";',
      "  const template = `import(\"bun:ffi\")`;",
      "  return term;",
      "}",
    ].join("\n");
    expect(hygieneViolations(clean)).toEqual([]);
    expect(importSpecifiers(clean)).toEqual(["./eval", "./term"]);
  });

  test("static import specifiers are found, dynamic ones are rejected separately", () => {
    expect(importSpecifiers('import { a } from "./a";\nexport * from "../b";')).toEqual(["./a", "../b"]);
    // `export * as ns from ...` and `export type * as ns from ...` used to slip through.
    expect(importSpecifiers('export * as ns from "bun:ffi";')).toEqual(["bun:ffi"]);
    expect(importSpecifiers('export type * as ns from "../b";')).toEqual(["../b"]);
    expect(importSpecifiers('import "node:fs";')).toEqual(["node:fs"]);
    expect(dynamicModuleReferences('import("./a");')).toEqual(["a dynamic `import(...)`"]);
    const computed = dynamicModuleReferences("const p = './a'; import(p);");
    expect(computed).toEqual(["a dynamic `import(...)`"]);
  });

  test("string spans and stripping behave for nested templates", () => {
    const { code, blanked } = stripSource("const s = `a${`b${c}`}d`; const t = 'x';");
    expect(code).toContain("c");
    expect(blanked).toContain("c");
    expect(blanked).not.toContain("a");
    expect(blanked).not.toContain("x");
  });
});
