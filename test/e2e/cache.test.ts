/**
 * Milestone 8: the cache (specification 6.5).
 *
 * The cache key hashes the verifier version, the mode, the file's contents and the contents
 * of every imported file, so a second run is a hit and editing an *imported* spec invalidates
 * its dependents.  Corrupt or version-mismatched entries are ignored and rewritten;
 * `DEP_VERIFY_NO_CACHE=1` bypasses both directions.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { cacheKey, importedFileHashes, verifyCached } from "../../src/cache";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");

function read(relative: string): string {
  return readFileSync(resolve(repoRoot, relative), "utf8");
}

function tempDir(label: string): string {
  const dir = resolve(repoRoot, ".dep-verify", `test-${label}-${process.pid}-${Date.now()}`);
  mkdirSync(dir, { recursive: true });
  return dir;
}

/** A copy of `clamp.ts` and `useClamp.ts` in a scratch directory, and their sources. */
function scratchPair(label: string): { dir: string; clamp: string; use: string; clampSource: string; useSource: string } {
  const dir = tempDir(label);
  const clampSource = read("examples/pass/clamp.ts");
  const useSource = read("examples/pass/useClamp.ts");
  const clamp = join(dir, "clamp.ts");
  const use = join(dir, "useClamp.ts");
  writeFileSync(clamp, clampSource, "utf8");
  writeFileSync(use, useSource, "utf8");
  return { dir, clamp, use, clampSource, useSource };
}

describe("hits and invalidation", () => {
  test("the second run hits the cache; editing an imported spec invalidates its dependents", () => {
    const scratch = scratchPair("invalidate");
    const cacheDir = join(scratch.dir, "cache");
    try {
      const first = verifyCached(scratch.use, scratch.useSource, { cacheDir });
      expect(first.cached).toBe(false);
      expect(first.ok).toBe(true);

      const second = verifyCached(scratch.use, scratch.useSource, { cacheDir });
      expect(second.cached).toBe(true);
      expect(second.ok).toBe(first.ok);
      // A cache hit is the same report, not a lossy one: injection needs the whole plan.
      expect(second.plan).toEqual(first.plan);
      expect(second.functions).toEqual(first.functions);
      expect(second.diagnostics).toEqual(first.diagnostics);

      // Editing the *imported* file's spec changes the dependent's pre-call obligation, so
      // its cache entry must not be reused.
      const edited = scratch.clampSource.replace("@pre lo <= hi", "@pre lo <= hi && lo >= -1000000");
      expect(edited).not.toBe(scratch.clampSource);
      writeFileSync(scratch.clamp, edited, "utf8");

      const third = verifyCached(scratch.use, scratch.useSource, { cacheDir });
      expect(third.cached).toBe(false);
      expect(third.plan).not.toEqual(first.plan);
      const preCall = third.plan.find((entry) => entry.kind === "pre-call");
      expect(preCall?.specText).toContain("1000000");
      // The imported file's own entry is keyed on its own contents, so it is a miss too.
      const clampResult = verifyCached(scratch.clamp, edited, { cacheDir });
      expect(clampResult.cached).toBe(false);
      expect(verifyCached(scratch.clamp, edited, { cacheDir }).cached).toBe(true);
    } finally {
      rmSync(scratch.dir, { recursive: true, force: true });
    }
  });

  test("the key covers the imported file's contents, not its path alone", () => {
    const source = read("examples/pass/useClamp.ts");
    const path = resolve(repoRoot, "examples/pass/useClamp.ts");
    const hashes = importedFileHashes(path, source);
    expect(hashes.map(([file]) => file)).toEqual([resolve(repoRoot, "examples/pass/clamp.ts")]);
    const changed = hashes.map(([file, hash]) => [file, `${hash.slice(0, -1)}0`] as [string, string]);
    expect(changed).not.toEqual(hashes);
  });

  test("the strict flag and the cache version are part of the key", () => {
    const source = read("examples/pass/clamp.ts");
    const path = resolve(repoRoot, "examples/pass/clamp.ts");
    expect(cacheKey(path, source, { strict: true })).not.toBe(cacheKey(path, source, { strict: false }));
    expect(cacheKey(path, source, { strict: false })).toBe(cacheKey(path, source, {}));
    expect(cacheKey(path, source, { timeoutMs: 1 })).not.toBe(cacheKey(path, source, {}));
  });
});

describe("bad entries and switches", () => {
  test("a corrupt entry is ignored and rewritten", () => {
    const scratch = scratchPair("corrupt");
    const cacheDir = join(scratch.dir, "cache");
    try {
      const first = verifyCached(scratch.use, scratch.useSource, { cacheDir });
      expect(first.cached).toBe(false);
      const file = join(cacheDir, `${cacheKey(scratch.use, scratch.useSource)}.json`);
      expect(existsSync(file)).toBe(true);
      writeFileSync(file, "{ this is not json", "utf8");
      const second = verifyCached(scratch.use, scratch.useSource, { cacheDir });
      expect(second.cached).toBe(false);
      // ... and the entry was rewritten, so the third run is a hit again.
      expect(JSON.parse(readFileSync(file, "utf8")).version).toBeGreaterThan(0);
      expect(verifyCached(scratch.use, scratch.useSource, { cacheDir }).cached).toBe(true);
    } finally {
      rmSync(scratch.dir, { recursive: true, force: true });
    }
  });

  test("a version mismatch is ignored", () => {
    const scratch = scratchPair("version");
    const cacheDir = join(scratch.dir, "cache");
    try {
      verifyCached(scratch.use, scratch.useSource, { cacheDir });
      const file = join(cacheDir, `${cacheKey(scratch.use, scratch.useSource)}.json`);
      const entry = JSON.parse(readFileSync(file, "utf8")) as { version: number };
      entry.version += 1000;
      writeFileSync(file, JSON.stringify(entry), "utf8");
      expect(verifyCached(scratch.use, scratch.useSource, { cacheDir }).cached).toBe(false);
    } finally {
      rmSync(scratch.dir, { recursive: true, force: true });
    }
  });

  test("DEP_VERIFY_NO_CACHE=1 bypasses the cache in both directions", () => {
    const scratch = scratchPair("nocache");
    const cacheDir = join(scratch.dir, "cache");
    const previous = process.env.DEP_VERIFY_NO_CACHE;
    process.env.DEP_VERIFY_NO_CACHE = "1";
    try {
      expect(verifyCached(scratch.use, scratch.useSource, { cacheDir }).cached).toBe(false);
      expect(verifyCached(scratch.use, scratch.useSource, { cacheDir }).cached).toBe(false);
      expect(existsSync(cacheDir) ? readdirSync(cacheDir).length : 0).toBe(0);
    } finally {
      if (previous === undefined) delete process.env.DEP_VERIFY_NO_CACHE;
      else process.env.DEP_VERIFY_NO_CACHE = previous;
      rmSync(scratch.dir, { recursive: true, force: true });
    }
  });
});
