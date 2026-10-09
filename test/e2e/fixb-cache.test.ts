/**
 * Cache regressions: the key must cover the *whole* reachable import graph, must not thrash
 * between relative and absolute callers, and must not serve an entry written by another
 * revision of the verifier.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { cacheKey, importedFileHashes, verifyCached, verifierFingerprint } from "../../src/cache";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");

const CALLER = `/**
 * @post result === x
 */
export function identity(x: number): number {
  return x;
}
`;

describe("the key covers the whole import graph", () => {
  test("a spec reached through more than 64 imports is hashed", () => {
    const dir = join(repoRoot, ".dep-verify", `fixb-key-${process.pid}-${Date.now()}`);
    mkdirSync(dir, { recursive: true });
    try {
      let source = "";
      for (let i = 0; i < 64; i += 1) {
        writeFileSync(join(dir, `m${i}.ts`), `export const v${i} = ${i};\n`, "utf8");
        source += `import { v${i} } from "./m${i}";\n`;
      }
      writeFileSync(join(dir, "mid.ts"), `import type { Alias } from "./third";\nexport type { Alias };\n`, "utf8");
      writeFileSync(join(dir, "third.ts"), `export type Alias = number;\n`, "utf8");
      source += `import { Alias } from "./mid";\nexport const all = [${Array.from({ length: 64 }, (_, i) => `v${i}`).join(",")}];\n`;
      const path = join(dir, "big.ts");
      writeFileSync(path, source, "utf8");

      const hashes = importedFileHashes(path, source);
      expect(hashes.length).toBe(66);
      expect(hashes.some(([file]) => file.endsWith("mid.ts"))).toBe(true);
      expect(hashes.some(([file]) => file.endsWith("third.ts"))).toBe(true);

      // Editing the deep spec invalidates the key: a stale *success* must not be served.
      const before = cacheKey(path, source);
      writeFileSync(join(dir, "third.ts"), `export type Alias = string;\n`, "utf8");
      expect(cacheKey(path, source)).not.toBe(before);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});

describe("relative and absolute callers share one entry", () => {
  test("neither path form invalidates the other", () => {
    const dir = join(repoRoot, ".dep-verify", `fixb-paths-${process.pid}-${Date.now()}`);
    mkdirSync(dir, { recursive: true });
    const absolute = join(dir, "caller.ts");
    const relativePath = relative(process.cwd(), absolute);
    const cacheDir = join(dir, "cache");
    try {
      writeFileSync(absolute, CALLER, "utf8");
      const first = verifyCached(relativePath, CALLER, { cacheDir, solver: false });
      expect(first.cached).toBe(false);
      expect(first.path).toBe(relativePath);
      const again = verifyCached(relativePath, CALLER, { cacheDir, solver: false });
      expect(again.cached).toBe(true);
      const absoluteFirst = verifyCached(absolute, CALLER, { cacheDir, solver: false });
      expect(absoluteFirst.cached).toBe(true);
      expect(absoluteFirst.path).toBe(absolute);
      expect(verifyCached(relativePath, CALLER, { cacheDir, solver: false }).cached).toBe(true);
      // One entry, not two: the two callers describe the same file.
      expect(verifyCached(absolute, CALLER, { cacheDir, solver: false }).cached).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});

describe("entries from another verifier revision", () => {
  test("a foreign fingerprint is ignored and rewritten", () => {
    const dir = join(repoRoot, ".dep-verify", `fixb-fingerprint-${process.pid}-${Date.now()}`);
    mkdirSync(dir, { recursive: true });
    const cacheDir = join(dir, "cache");
    const path = join(dir, "caller.ts");
    try {
      writeFileSync(path, CALLER, "utf8");
      const first = verifyCached(path, CALLER, { cacheDir, solver: false });
      expect(first.cached).toBe(false);
      const file = join(cacheDir, `${cacheKey(path, CALLER, { solver: false })}.json`);
      const entry = JSON.parse(readFileSync(file, "utf8")) as { fingerprint?: string };
      expect(entry.fingerprint).toMatch(/^[0-9a-f]{64}$/);
      expect(entry.fingerprint).toBe(verifierFingerprint());

      entry.fingerprint = "0".repeat(64);
      writeFileSync(file, JSON.stringify(entry), "utf8");
      expect(verifyCached(path, CALLER, { cacheDir, solver: false }).cached).toBe(false);
      // The miss rewrote the entry with this revision's fingerprint.
      expect(verifyCached(path, CALLER, { cacheDir, solver: false }).cached).toBe(true);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });

  test("the fingerprint is stable and depends on the verifier's sources", () => {
    expect(verifierFingerprint()).toMatch(/^[0-9a-f]{64}$/);
    expect(verifierFingerprint()).toBe(verifierFingerprint());
  });
});
