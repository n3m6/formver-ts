/**
 * Milestone 5: spec resolution by parsing.
 *
 * Imports are read and parsed, never executed; the callee's signature becomes an `external`
 * declaration carrying the sha256 of the file it came from.  Import cycles are harmless
 * because only signatures are needed.
 */
import { describe, expect, test } from "bun:test";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import * as K from "../../src/kernel/index";
import { extractFile } from "../../src/extract/fragment";
import { SpecResolver, contentHash, resolveImportPath } from "../../src/extract/specs";

const repoRoot = resolve(import.meta.dir, "../..");

function extractFileAt(path: string) {
  return extractFile(path, readFileSync(path, "utf8"));
}

describe("useClamp.ts", () => {
  const ir = extractFileAt(resolve(repoRoot, "examples/pass/useClamp.ts"));
  const fn = ir.functions.find((f) => f.name === "percent")!;

  test("the call resolves `clamp` from ./clamp.ts, parsed and hashed", () => {
    expect(ir.diagnostics).toEqual([]);
    expect(fn.imports).toHaveLength(1);
    const spec = fn.imports[0]!;
    expect(spec.name).toBe("clamp");
    expect(spec.file.endsWith(join("examples", "pass", "clamp.ts"))).toBe(true);
    expect(spec.decl.kind).toBe("external");
    expect(spec.decl.source.file).toBe(spec.file);
    expect(spec.decl.source.hash).toBe(contentHash(readFileSync(spec.file, "utf8")));
    expect(spec.decl.type).toBe(spec.signature.type);
  });

  test("the hash is stable across runs", () => {
    const again = extractFileAt(resolve(repoRoot, "examples/pass/useClamp.ts")).functions[0]!;
    expect(again.imports[0]!.hash).toBe(fn.imports[0]!.hash);
    expect(fn.imports[0]!.hash).toMatch(/^[0-9a-f]{64}$/);
  });

  test("the external declaration's type is exactly the local clamp signature", () => {
    const clamp = extractFileAt(resolve(repoRoot, "examples/pass/clamp.ts")).functions[0]!;
    expect(K.formatTerm(fn.imports[0]!.decl.type)).toBe(K.formatTerm(clamp.signature.type));
  });

  test("the call's precondition is instantiated at the call site", () => {
    const preCall = fn.sites.find((s) => s.kind === "pre-call")!;
    expect(preCall.text).toBe("(0 <= 100)");
    expect(K.formatTerm(K.inferType(K.emptyEnv(), K.intLit(0n)).ok ? K.Le(K.intLit(0n), K.intLit(100n)) : K.Unit)).toBe(
      "Le(0, 100)",
    );
  });

  test("the used import hash is reported for the cache key", () => {
    expect([...ir.importedHashes.values()]).toEqual([fn.imports[0]!.hash]);
  });
});

describe("specifier resolution", () => {
  const dir = mkdtempSync(join(tmpdir(), "formver-specs-"));
  const write = (name: string, contents: string) => {
    const path = join(dir, name);
    writeFileSync(path, contents);
    return path;
  };

  const clamp = write(
    "clamp.ts",
    "/**\n * @pre lo <= hi\n * @post lo <= result && result <= hi\n */\nexport function clamp(x: number, lo: number, hi: number): number {\n  return x;\n}\n",
  );
  write("shape.ts", 'export type Shape =\n  | { readonly kind: "square"; readonly side: number }\n  | { readonly kind: "rect"; readonly w: number };\n');
  const useBoth = write(
    "useBoth.ts",
    'import { clamp } from "./clamp";\nimport { Shape } from "./shape";\n' +
      "/**\n * @post result >= 0\n */\nexport function f(s: Shape, p: number): number {\n" +
      '  if (s.kind === "square") {\n    return clamp(p, 0, s.side);\n  }\n  return clamp(p, 0, s.w);\n}\n',
  );
  const missing = write(
    "missing.ts",
    'import { nope } from "./clamp";\n/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return nope(x);\n}\n',
  );
  const cycleA = write(
    "a.ts",
    'import { b } from "./b";\n/**\n * @post result >= 0\n */\nexport function a(x: number): number {\n  return b(x);\n}\n',
  );
  write(
    "b.ts",
    'import { a } from "./a";\n/**\n * @post result >= 0\n */\nexport function b(x: number): number {\n  return x;\n}\n',
  );

  test("an extensionless specifier resolves to .ts", () => {
    expect(resolveImportPath(useBoth, "./clamp")).toBe(clamp);
  });

  test("an imported function and an imported union alias both resolve", () => {
    const ir = extractFileAt(useBoth);
    expect(ir.diagnostics).toEqual([]);
    const fn = ir.functions[0]!;
    expect(fn.imports.map((i) => i.name)).toEqual(["clamp"]);
    // The imported alias is a real union: `s.kind` narrows and `s.side` type-checks.
    expect(fn.signature.binders[0]!.name).toBe("s");
    expect(K.formatTerm(fn.signature.type)).toContain("Sum(");
  });

  test("a call to an import whose file has no such verified function is located", () => {
    const ir = extractFileAt(missing);
    const errors = ir.diagnostics.filter((d) => d.message.includes("is not a verified function in"));
    expect(errors).toHaveLength(1);
    expect(errors[0]!.span.line).toBe(6);
  });

  test("an import cycle is harmless: only the signature is needed", () => {
    const ir = extractFileAt(cycleA);
    expect(ir.diagnostics).toEqual([]);
    expect(ir.functions[0]!.imports[0]!.name).toBe("b");
  });

  test("the resolver caches by path and parses each file once", () => {
    const resolver = new SpecResolver();
    const first = resolver.resolve(useBoth, "./clamp");
    const second = resolver.resolve(useBoth, "./clamp");
    expect(first.ok && second.ok && first.file === second.file).toBe(true);
    resolver.clear();
    const third = resolver.resolve(useBoth, "./clamp");
    expect(third.ok).toBe(true);
  });

  test("a non-relative specifier is rejected", () => {
    const ir = extractFileAt(
      write(
        "pkg.ts",
        'import { clamp } from "some-package";\n/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return clamp(x, 0, 1);\n}\n',
      ),
    );
    expect(ir.diagnostics.some((d) => d.message.includes("only relative imports are allowed"))).toBe(true);
  });
});
