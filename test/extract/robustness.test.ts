/**
 * Milestone 5: extraction never throws.
 *
 * The fragment checker runs over every `.ts` file in the repository (most of which are not in
 * the verified fragment at all) and must always come back with located diagnostics, never an
 * exception.  Failures inside the extraction layer itself become `internal` diagnostics.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { relative, resolve } from "node:path";
import { extractFile } from "../../src/extract/fragment";
import { formatDiagnostic } from "../../src/diagnostics";

const repoRoot = resolve(import.meta.dir, "../..");

function repositoryFiles(): string[] {
  const files: string[] = [];
  for (const dir of ["src", "test", "scripts", "examples"]) {
    const glob = new Bun.Glob(`${dir}/**/*.{ts,mts}`);
    for (const path of glob.scanSync({ cwd: repoRoot, absolute: true })) files.push(path);
  }
  return files.sort();
}

describe("robustness", () => {
  test("every repository file extracts without throwing", () => {
    const files = repositoryFiles();
    expect(files.length).toBeGreaterThan(20);
    for (const path of files) {
      const source = readFileSync(path, "utf8");
      let ir;
      try {
        ir = extractFile(path, source);
      } catch (error) {
        throw new Error(`${relative(repoRoot, path)} threw: ${String(error)}`);
      }
      // Diagnostics must be sorted and located in the file they came from.
      for (const diagnostic of ir.diagnostics) {
        expect(typeof formatDiagnostic(diagnostic)).toBe("string");
        expect(diagnostic.span.line).toBeGreaterThan(0);
        expect(diagnostic.span.col).toBeGreaterThan(0);
      }
      const internals = ir.diagnostics.filter((d) => d.kind === "internal");
      expect({ file: relative(repoRoot, path), internals: internals.map((d) => d.message) }).toEqual({
        file: relative(repoRoot, path),
        internals: [],
      });
    }
  });

  test("garbage inside an annotated function yields diagnostics, not exceptions", () => {
    const sources = [
      "/**\n * @post result >= 0\n */\nexport function f( { return ; }\n",
      "/**\n * @pre\n */\nexport function f(x: number): number {\n  return x;\n}\n",
      "/**\n * @post result >= \n */\nexport function f(x: number): number {\n  return x;\n}\n",
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return (((((x;\n}\n",
      "/**\n * @post 1.5\n */\nexport function f(x: number): number {\n  return x;\n}\n",
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  let i = 0;\n  while (i < x) {\n    i = i + 1;\n  }\n  return i;\n}\n",
    ];
    for (const source of sources) {
      const ir = extractFile("synthetic.ts", source);
      expect(ir.diagnostics.length).toBeGreaterThan(0);
      expect(ir.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
    }
  });
});
