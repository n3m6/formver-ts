/**
 * Repository hygiene tests.
 *
 * Two hard rules from the design (section 2):
 *   - `package.json` has no runtime dependencies, ever.
 *   - `src/kernel/` (the only trusted component) imports nothing from outside itself,
 *     and uses neither Bun APIs nor npm packages.
 *
 * Both tests must pass before `src/kernel/` exists, so the kernel scan only runs when the
 * directory is present.
 */
import { describe, expect, test } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { dirname, relative, resolve, sep } from "node:path";

const repoRoot = resolve(import.meta.dir, "..");
const packageJsonPath = resolve(repoRoot, "package.json");
const kernelDir = resolve(repoRoot, "src/kernel");

type PackageJson = Record<string, unknown>;

function readPackageJson(): PackageJson {
  const parsed: unknown = JSON.parse(readFileSync(packageJsonPath, "utf8"));
  if (typeof parsed !== "object" || parsed === null || Array.isArray(parsed)) {
    throw new Error("package.json is not an object");
  }
  return parsed as PackageJson;
}

describe("package.json", () => {
  const pkg = readPackageJson();

  test("has no `dependencies` key", () => {
    expect(Object.hasOwn(pkg, "dependencies")).toBe(false);
  });

  test("has no non-empty dependencies object under any dependency field", () => {
    for (const field of ["dependencies", "optionalDependencies", "peerDependencies"] as const) {
      const value = pkg[field];
      if (value === undefined) continue;
      expect(typeof value).toBe("object");
      expect(Object.keys(value as Record<string, unknown>)).toEqual([]);
    }
  });

  test("declares only the type-checking devDependencies", () => {
    expect(pkg["devDependencies"]).toEqual({
      typescript: expect.any(String),
      "@types/bun": expect.any(String),
    });
  });
});

/** Kernel files, or an empty list when `src/kernel/` does not exist yet. */
function kernelFiles(): string[] {
  if (!existsSync(kernelDir)) return [];
  return [...new Bun.Glob("**/*.{ts,mts}").scanSync({ cwd: kernelDir, absolute: true })].sort();
}

/**
 * Remove comments, and optionally blank string/template literal contents. String contents
 * must be kept when scanning for import specifiers, but must be blanked before looking for
 * the `Bun` global, so that prose and strings cannot trip the check. Regex literals are not
 * handled; the kernel has no business containing any, and mis-lexing one can only produce
 * false negatives here.
 */
function stripSource(source: string, blankStrings: boolean): string {
  let out = "";
  let i = 0;
  while (i < source.length) {
    const ch = source[i]!;
    const next = source[i + 1];
    if (ch === "/" && next === "/") {
      while (i < source.length && source[i] !== "\n") i += 1;
      continue;
    }
    if (ch === "/" && next === "*") {
      i += 2;
      while (i < source.length && !(source[i] === "*" && source[i + 1] === "/")) i += 1;
      i += 2;
      out += " ";
      continue;
    }
    if (ch === '"' || ch === "'" || ch === "`") {
      const quote = ch;
      const start = i;
      i += 1;
      while (i < source.length && source[i] !== quote) {
        if (source[i] === "\\") i += 1;
        i += 1;
      }
      i += 1;
      out += blankStrings ? (quote === "`" ? "``" : '""') : source.slice(start, i);
      continue;
    }
    out += ch;
    i += 1;
  }
  return out;
}

/** Every module specifier referenced by static imports, re-exports, require or import(). */
function importSpecifiers(source: string): string[] {
  const specifiers: string[] = [];
  const patterns = [
    /\bimport\s+(?:type\s+)?(?:[^"'`;]*?\bfrom\s*)?["']([^"']+)["']/g, // import x from "m"; import "m"
    /\bexport\s+(?:type\s+)?(?:\*|\{[^}]*\})\s*from\s*["']([^"']+)["']/g, // export ... from "m"
    /\brequire\s*\(\s*["']([^"']+)["']\s*\)/g,
    /\bimport\s*\(\s*["']([^"']+)["']\s*\)/g,
  ];
  const code = stripSource(source, false);
  for (const pattern of patterns) {
    for (const match of code.matchAll(pattern)) {
      specifiers.push(match[1]!);
    }
  }
  return specifiers;
}

function resolvesInsideKernel(fromFile: string, specifier: string): boolean {
  if (!specifier.startsWith("./") && !specifier.startsWith("../")) return false;
  const withoutQuery = specifier.replace(/[?#].*$/, "");
  const base = resolve(dirname(fromFile), withoutQuery);
  const candidates = [base, `${base}.ts`, `${base}.mts`, resolve(base, "index.ts")];
  if (base.endsWith(".js")) {
    // Allow the `./x.js` spelling of a TypeScript source file.
    candidates.push(`${base.slice(0, -3)}.ts`, `${base.slice(0, -3)}.mts`);
  }
  const target = candidates.find((candidate) => existsSync(candidate));
  if (target === undefined) return false;
  const inside = relative(kernelDir, target);
  return inside.length > 0 && !inside.startsWith("..") && !inside.startsWith(`..${sep}`);
}

/** Ways of naming the Bun global in code that has been stripped of comments and strings. */
const BUN_GLOBAL_PATTERNS = [/(^|[^\w.$])Bun\b/, /globalThis\s*\.\s*Bun\b/];

describe("src/kernel/ hygiene", () => {
  const files = kernelFiles();

  test("imports only relative paths that resolve inside src/kernel/", () => {
    const violations: string[] = [];
    for (const file of files) {
      const source = readFileSync(file, "utf8");
      for (const specifier of importSpecifiers(source)) {
        if (!resolvesInsideKernel(file, specifier)) {
          violations.push(`${relative(repoRoot, file)} imports ${JSON.stringify(specifier)}`);
        }
      }
    }
    expect(violations).toEqual([]);
  });

  test("does not reference the Bun global", () => {
    const violations: string[] = [];
    for (const file of files) {
      const code = stripSource(readFileSync(file, "utf8"), true);
      if (BUN_GLOBAL_PATTERNS.some((pattern) => pattern.test(code))) {
        violations.push(relative(repoRoot, file));
      }
    }
    expect(violations).toEqual([]);
  });
});
