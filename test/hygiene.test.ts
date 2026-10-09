/**
 * Repository hygiene tests.
 *
 * Two hard rules from the design (section 2):
 *   - `package.json` has no runtime dependencies, ever.
 *   - `src/kernel/` (the only trusted component) imports nothing from outside itself, and
 *     uses neither Bun APIs, nor npm packages, nor ambient host globals.
 *
 * The kernel scan is deliberately paranoid: it blanks comments and string contents (template
 * literals included, keeping `${…}` interpolations visible), rejects every non-static module
 * reference (`import(variable)`, `require`, aliased or not) and every ambient global, and
 * resolves import targets through `realpathSync` so a symlink cannot point outside the
 * kernel.  `test/hygiene-checker.test.ts` feeds this checker adversarial sources.
 */
import { describe, expect, test } from "bun:test";
import { existsSync, readFileSync, realpathSync } from "node:fs";
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
export function kernelFiles(dir: string = kernelDir): string[] {
  if (!existsSync(dir)) return [];
  return [...new Bun.Glob("**/*.{ts,mts}").scanSync({ cwd: dir, absolute: true })].sort();
}

export interface Stripped {
  /** Comments removed; string contents kept (so specifiers are visible). */
  readonly code: string;
  /** `[start, end)` ranges of string-literal contents inside `code`. */
  readonly strings: Array<[number, number]>;
  /** Comments and string contents removed, so only executable code remains. */
  readonly blanked: string;
}

/**
 * Strip comments and record string spans.  Template literals keep their `${…}`
 * interpolations visible (recursively stripped) and have their literal text blanked, so a
 * host global cannot hide inside an interpolation and an import mentioned inside a literal
 * cannot produce a false positive.
 */
export function stripSource(source: string): Stripped {
  let code = "";
  let blanked = "";
  const strings: Array<[number, number]> = [];

  const emitLiteral = (raw: string, content: string): void => {
    code += raw;
    const start = blanked.length;
    blanked += '""';
    strings.push([start, start]);
    void content;
  };

  const scanString = (i: number, quote: string): number => {
    const start = i;
    i += 1;
    while (i < source.length && source[i] !== quote) {
      if (source[i] === "\\") i += 1;
      i += 1;
    }
    i += 1;
    emitLiteral(source.slice(start, i), source.slice(start + 1, i - 1));
    return i;
  };

  const scanTemplate = (i: number): number => {
    i += 1; // the opening backtick
    let chunk = "`";
    while (i < source.length && source[i] !== "`") {
      if (source[i] === "\\") {
        chunk += source.slice(i, i + 2);
        i += 2;
        continue;
      }
      if (source[i] === "$" && source[i + 1] === "{") {
        emitLiteral(chunk + "${", "");
        chunk = "";
        i += 2;
        let depth = 1;
        const innerStart = i;
        while (i < source.length && depth > 0) {
          const ch = source[i]!;
          if (ch === "{") depth += 1;
          else if (ch === "}") depth -= 1;
          if (depth === 0) break;
          if (ch === '"' || ch === "'") {
            i = scanString(i, ch);
            continue;
          }
          if (ch === "`") {
            i = scanTemplate(i);
            continue;
          }
          i += 1;
        }
        // Recursively strip the interpolation so its code counts as code.
        const inner = stripSource(source.slice(innerStart, i));
        code += inner.code;
        blanked += inner.blanked;
        chunk = "}";
        i += 1;
        continue;
      }
      chunk += source[i];
      i += 1;
    }
    i += 1; // the closing backtick
    emitLiteral(`${chunk}\``, chunk);
    return i;
  };

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
      code += " ";
      blanked += " ";
      continue;
    }
    if (ch === '"' || ch === "'") {
      i = scanString(i, ch);
      continue;
    }
    if (ch === "`") {
      i = scanTemplate(i);
      continue;
    }
    code += ch;
    blanked += ch;
    i += 1;
  }
  return { code, strings, blanked };
}

const inside = (spans: ReadonlyArray<[number, number]>, index: number): boolean =>
  spans.some(([start, end]) => index >= start && index < end);

/** Module specifiers of static imports/re-exports; matches inside string literals are ignored. */
export function importSpecifiers(source: string): string[] {
  const { code, strings } = stripSource(source);
  const patterns = [
    /\bimport\s+(?:type\s+)?(?:[^"'`;]*?\bfrom\s*)?["']([^"']+)["']/g, // import x from "m"; import "m"
    /\bfrom\s*["']([^"']+)["']/g, // export ... from "m", including `export * as ns from "m"`
  ];
  const found = new Set<string>();
  for (const pattern of patterns) {
    for (const match of code.matchAll(pattern)) {
      const specIndex = match.index + match[0].indexOf(match[1]!);
      if (inside(strings, specIndex)) continue;
      found.add(match[1]!);
    }
  }
  return [...found];
}

/** Ambient host capabilities the trusted kernel must never touch. */
const FORBIDDEN_PATTERNS: ReadonlyArray<readonly [string, RegExp]> = [
  ["the Bun global", /(^|[^\w.$])Bun\b/],
  ["globalThis", /\bglobalThis\b/],
  ["the `global` object", /\bglobal\b/],
  ["the `self` global", /\bself\b/],
  ["the `window` global", /\bwindow\b/],
  ["the `process` global", /\bprocess\b/],
  ["the `console` global", /\bconsole\b/],
  ["the `Buffer` global", /\bBuffer\b/],
  ["`require`", /\brequire\b/],
  ["the `Deno` global", /\bDeno\b/],
  ["`import.meta`", /\bimport\s*\.\s*meta\b/],
  ["`eval`", /\beval\s*\(/],
  ["the `Function` constructor", /\bFunction\s*\(/],
  ["`setTimeout`/`setInterval`", /\bset(?:Timeout|Interval)\s*\(/],
  ["`fetch`", /\bfetch\s*\(/],
  ["`WebAssembly`", /\bWebAssembly\b/],
  ["`TextEncoder`/`TextDecoder`", /\bText(?:En|De)coder\b/],
  ["`crypto`", /\bcrypto\b/],
  ["`performance`", /\bperformance\b/],
];

/** Every non-static module reference: any `import(...)` or `require`, aliased or not. */
export function dynamicModuleReferences(source: string): string[] {
  const { blanked } = stripSource(source);
  const found: string[] = [];
  if (/\bimport\s*\(/.test(blanked)) found.push("a dynamic `import(...)`");
  if (/\brequire\s*\(/.test(blanked)) found.push("`require(...)`");
  if (/\brequire\b/.test(blanked)) found.push("a `require` reference");
  return found;
}

/** Forbidden ambient-global or dynamic-module uses in a source file. */
export function hygieneViolations(source: string): string[] {
  const { blanked } = stripSource(source);
  const violations: string[] = [];
  for (const [what, pattern] of FORBIDDEN_PATTERNS) {
    if (pattern.test(blanked)) violations.push(what);
  }
  violations.push(...dynamicModuleReferences(source));
  return [...new Set(violations)];
}

export function resolvesInsideKernel(fromFile: string, specifier: string, kernel: string = kernelDir): boolean {
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
  // `realpathSync` so a symlink inside the kernel cannot point outside it.
  const real = realpathSync(target);
  const realKernel = realpathSync(kernel);
  const inside_ = relative(realKernel, real);
  return inside_.length > 0 && !inside_.startsWith("..") && !inside_.startsWith(`..${sep}`);
}

describe("src/kernel/ hygiene", () => {
  const files = kernelFiles();

  test("imports only relative paths that resolve inside src/kernel/", () => {
    const violations: string[] = [];
    for (const file of files) {
      for (const specifier of importSpecifiers(readFileSync(file, "utf8"))) {
        if (!resolvesInsideKernel(file, specifier)) {
          violations.push(`${relative(repoRoot, file)} imports ${JSON.stringify(specifier)}`);
        }
      }
    }
    expect(violations).toEqual([]);
  });

  test("uses no Bun API, npm package, ambient global or dynamic module reference", () => {
    const violations: string[] = [];
    for (const file of files) {
      for (const what of hygieneViolations(readFileSync(file, "utf8"))) {
        violations.push(`${relative(repoRoot, file)} uses ${what}`);
      }
    }
    expect(violations).toEqual([]);
  });
});
