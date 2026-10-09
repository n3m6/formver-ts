/**
 * Verification cache (specification 6.5).
 *
 * `.dep-verify/cache/<sha256>.json`, where the file name hashes
 *
 *   - `CACHE_VERSION` (bump it whenever `verify()`'s output changes shape or meaning),
 *   - the strict flag and the Z3 timeout the verdicts were computed with,
 *   - the **contents** of the file being verified, and
 *   - the contents of every file it imports, transitively.
 *
 * The import hashes are what make the cache correct rather than merely fast: an imported
 * file's specs are `external` declarations of the importing file, so editing an imported
 * `@pre`/`@post` must invalidate every dependent.  A corrupt entry, an entry written by
 * another cache version, or one whose key no longer matches is ignored and then rewritten.
 *
 * `DEP_VERIFY_NO_CACHE=1` bypasses the cache in both directions.  Everything here is
 * synchronous, because the plugin's `onLoad` must be (section 3.1 point 5).
 */
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { relative, resolve } from "node:path";
import { contentHash, resolveImportPath } from "./extract/specs";
import { parseFile } from "./syntax/parser";
import { verify, type VerifyResult } from "./verify";
import { isAvailable } from "./vc/z3";

/**
 * The cache format version.  Bump it whenever the *shape* of an entry changes; a change in
 * verification *semantics* is covered automatically by `verifierFingerprint()`.
 */
export const CACHE_VERSION = 2;

/** `.dep-verify/cache/`, resolved from this file rather than from the process cwd. */
export const CACHE_DIR: string = resolve(import.meta.dir, "..", ".dep-verify", "cache");

/** A `verify()` result without the kernel environment, which is not serializable. */
export type VerifyReport = Omit<VerifyResult, "env">;

export interface VerifyCachedOptions {
  readonly strict?: boolean;
  readonly timeoutMs?: number;
  /** Overrides `.dep-verify/cache/` (used by tests). */
  readonly cacheDir?: string;
  /** Bypass the cache; `DEP_VERIFY_NO_CACHE=1` does the same. */
  readonly noCache?: boolean;
  /** File reader for imported specs; defaults to `node:fs`. */
  readonly readFile?: (path: string) => string;
  /**
   * Whether an SMT solver was available for the verdicts.  Defaults to `z3.isAvailable()`;
   * it is part of the key, because a report computed without a solver says nothing about
   * what a run with one would prove.
   */
  readonly solver?: boolean;
  /**
   * Verify the imported files too, so a caller of an uncertified import is marked (section
   * 6.5).  Defaults to the strict flag: strict mode's guarantee — every obligation
   * kernel-certified, every imported spec certified in its own file — must not depend on
   * which entry point (CLI, `bun run`, `Bun.build`) verified the file.
   */
  readonly verifyImports?: boolean;
}

export interface CachedVerifyReport extends VerifyReport {
  /** True when the report came from the cache instead of a fresh verification. */
  readonly cached: boolean;
}

interface CacheEntry {
  readonly version: number;
  readonly key: string;
  readonly path: string;
  readonly sourceHash: string;
  readonly imports: readonly (readonly [string, string])[];
  /** `verifierFingerprint()` of the revision that wrote the entry. */
  readonly fingerprint?: string;
  readonly report: VerifyReport;
}

/** The `DEP_VERIFY_NO_CACHE=1` switch (any other value keeps the cache on). */
export function cacheDisabled(): boolean {
  return process.env.DEP_VERIFY_NO_CACHE === "1";
}

/**
 * `[path, contentHash]` for the file and **every** file it imports, transitively, sorted by
 * path.  The whole reachable graph is hashed: the spec of a type alias re-exported through
 * `mid.ts` (which `src/extract/specs.ts` resolves) would otherwise be invisible to the key
 * and a stale *success* verdict could be served.  Cycles end at the `out.has` check.
 *
 * Missing, unreadable and unresolvable imports are skipped: the verification itself reports
 * them, and the key must stay stable while they are broken.
 */
export function importedFileHashes(
  path: string,
  source: string,
  read: (file: string) => string = (file) => readFileSync(file, "utf8"),
): [string, string][] {
  const out = new Map<string, string>();
  const visit = (file: string, text: string): void => {
    let imports;
    try {
      imports = parseFile(file, text).imports;
    } catch {
      return;
    }
    for (const declaration of imports) {
      const target = resolveImportPath(file, declaration.specifier);
      if (target === null || out.has(target)) continue;
      let contents: string;
      try {
        contents = read(target);
      } catch {
        continue;
      }
      out.set(target, contentHash(contents));
      visit(target, contents);
    }
  };
  visit(path, source);
  return [...out.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
}

/**
 * A fingerprint of this verifier's own sources.  A verdict is only reusable while the code
 * that produced it is unchanged; `CACHE_VERSION` is a manual constant, so the fingerprint
 * makes every edit to `src/**` invalidate every entry by itself.  Memoized per process.
 */
let fingerprint: string | undefined;

export function verifierFingerprint(): string {
  if (fingerprint !== undefined) return fingerprint;
  const root = import.meta.dir; // src/
  const files: string[] = [];
  const walk = (dir: string): void => {
    let entries;
    try {
      entries = readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of [...entries].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0))) {
      const full = resolve(dir, entry.name);
      if (entry.isDirectory()) walk(full);
      else if (entry.isFile() && entry.name.endsWith(".ts")) files.push(full);
    }
  };
  walk(root);
  const hasher = new Bun.CryptoHasher("sha256");
  for (const file of files) {
    hasher.update(`${relative(root, file)}\n`);
    try {
      hasher.update(readFileSync(file));
    } catch {
      hasher.update("<unreadable>");
    }
    hasher.update("\n");
  }
  fingerprint = hasher.digest("hex");
  return fingerprint;
}

/** Absolute path, so a relative and an absolute caller share one entry instead of thrashing. */
function normalisePath(path: string): string {
  return resolve(path);
}

/** The sha256 cache key: version, verifier sources, mode, the file's hash and every import's. */
export function cacheKey(path: string, source: string, options: VerifyCachedOptions = {}): string {
  const imports = importedFileHashes(path, source, options.readFile);
  const hasher = new Bun.CryptoHasher("sha256");
  hasher.update(
    JSON.stringify([
      CACHE_VERSION,
      verifierFingerprint(),
      normalisePath(path),
      options.strict === true,
      options.timeoutMs ?? 0,
      options.solver ?? isAvailable(),
      options.verifyImports ?? options.strict === true,
      contentHash(source),
      imports,
    ]),
  );
  return hasher.digest("hex");
}

function isReport(value: unknown): value is VerifyReport {
  if (typeof value !== "object" || value === null) return false;
  const report = value as Partial<VerifyReport>;
  return (
    typeof report.path === "string" &&
    typeof report.strict === "boolean" &&
    typeof report.ok === "boolean" &&
    Array.isArray(report.functions) &&
    Array.isArray(report.diagnostics) &&
    Array.isArray(report.plan) &&
    Array.isArray(report.externals) &&
    Array.isArray(report.axioms)
  );
}

function readEntry(file: string, key: string, path: string): VerifyReport | undefined {
  let text: string;
  try {
    text = readFileSync(file, "utf8");
  } catch {
    return undefined;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    return undefined;
  }
  if (typeof parsed !== "object" || parsed === null) return undefined;
  const entry = parsed as Partial<CacheEntry>;
  if (entry.version !== CACHE_VERSION || entry.key !== key) return undefined;
  // An entry from another revision of the verifier says nothing about this one.
  if (entry.fingerprint !== verifierFingerprint()) return undefined;
  const report = entry.report;
  // Compare resolved paths: the plugin passes absolute paths and `scripts/demo.ts` relative
  // ones, and both describe the same file.
  if (!isReport(report) || normalisePath(report.path) !== normalisePath(path)) return undefined;
  return report;
}

function writeEntry(file: string, entry: CacheEntry): void {
  try {
    mkdirSync(resolve(file, ".."), { recursive: true });
    writeFileSync(file, `${JSON.stringify(entry)}\n`, "utf8");
  } catch {
    // A cache that cannot be written is not an error: verification already succeeded.
  }
}

/**
 * `verify()` with the content-addressed cache in front of it.  The returned report is exactly
 * what `verify()` returns (minus the kernel environment) plus a `cached` flag, so callers —
 * the plugin — cannot tell a hit from a miss except by the flag.
 */
export function verifyCached(
  path: string,
  source: string,
  options: VerifyCachedOptions = {},
): CachedVerifyReport {
  const cacheDir = options.cacheDir ?? CACHE_DIR;
  const disabled = options.noCache === true || cacheDisabled();
  const key = cacheKey(path, source, options);
  const file = resolve(cacheDir, `${key}.json`);
  if (!disabled) {
    const hit = readEntry(file, key, path);
    // The caller's own path, not the one the entry happened to be written with.
    if (hit !== undefined) return { ...hit, path, cached: true };
  }
  const result = verify(path, source, {
    strict: options.strict ?? false,
    solver: options.solver ?? isAvailable(),
    verifyImports: options.verifyImports ?? options.strict === true,
    ...(options.timeoutMs === undefined ? {} : { timeoutMs: options.timeoutMs }),
    ...(options.readFile === undefined ? {} : { readFile: options.readFile }),
  });
  const report: VerifyReport = {
    path,
    strict: result.strict,
    ok: result.ok,
    functions: result.functions,
    diagnostics: result.diagnostics,
    plan: result.plan,
    externals: result.externals,
    axioms: result.axioms,
  };
  if (!disabled) {
    writeEntry(file, {
      version: CACHE_VERSION,
      key,
      path: normalisePath(path),
      sourceHash: contentHash(source),
      imports: importedFileHashes(path, source, options.readFile),
      fingerprint: verifierFingerprint(),
      report: { ...report, path: normalisePath(path) },
    });
  }
  return { ...report, cached: false };
}
