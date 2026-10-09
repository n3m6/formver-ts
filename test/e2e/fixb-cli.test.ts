/**
 * CLI regression: a requested file with no annotated function verified nothing, yet the run
 * reported "1 file(s) verified" and exited 0.  The summary now counts functions, and a file
 * that yields no verdict at all is an error.
 */
import { afterAll, describe, expect, setDefaultTimeout, test } from "bun:test";
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { CACHE_DIR, cacheKey } from "../../src/cache";
import { run } from "../../src/cli";
import { isAvailable } from "../../src/vc/z3";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");
const SCRATCH = join(repoRoot, ".dep-verify", `fixb-cli-${process.pid}-${Date.now()}`);
mkdirSync(SCRATCH, { recursive: true });
afterAll(() => rmSync(SCRATCH, { recursive: true, force: true }));

interface Captured {
  readonly code: number;
  readonly stdout: string;
  readonly stderr: string;
}

/** Run the CLI in-process, capturing everything it prints. */
function cli(argv: readonly string[]): Captured {
  const log = console.log;
  const error = console.error;
  const warn = console.warn;
  let stdout = "";
  let stderr = "";
  console.log = (...args: unknown[]) => {
    stdout += `${args.map((value) => String(value)).join(" ")}\n`;
  };
  console.error = (...args: unknown[]) => {
    stderr += `${args.map((value) => String(value)).join(" ")}\n`;
  };
  console.warn = (...args: unknown[]) => {
    stderr += `${args.map((value) => String(value)).join(" ")}\n`;
  };
  try {
    return { code: run([...argv]), stdout, stderr };
  } finally {
    console.log = log;
    console.error = error;
    console.warn = warn;
  }
}

describe("a file with nothing to verify", () => {
  test("is an error, not a silent success", () => {
    const path = join(SCRATCH, "empty.ts");
    writeFileSync(path, "", "utf8");
    const result = cli([path]);
    expect(result.code).toBe(1);
    expect(result.stderr).toContain("no annotated function to verify");
    expect(result.stdout).toContain("1 file(s) verified, 0 function(s) with a verdict");
  });

  test("even when another file in the same run verifies", () => {
    const empty = join(SCRATCH, "empty2.ts");
    const good = join(SCRATCH, "good.ts");
    writeFileSync(empty, "export const x = 1;\n", "utf8");
    writeFileSync(good, `/** @post result === x */\nexport function identity(x: number): number {\n  return x;\n}\n`, "utf8");
    const result = cli([empty, good]);
    expect(result.code).toBe(1);
    expect(result.stderr).toContain(`no annotated function to verify`);
    expect(result.stdout).toContain("2 file(s) verified, 1 function(s) with a verdict");
  });
});

describe("the summary counts functions", () => {
  test("a verified function shows up in the totals line", () => {
    const path = join(SCRATCH, "one.ts");
    writeFileSync(path, `/** @post result === x */\nexport function identity(x: number): number {\n  return x;\n}\n`, "utf8");
    const result = cli([path]);
    expect(result.code).toBe(0);
    expect(result.stdout).toMatch(/total\s+1\s+0\s+0\s+0/);
    expect(result.stdout).toContain("1 file(s) verified, 1 function(s) with a verdict");
    expect(result.stdout).toContain("axioms used: 0");
  });
});

describe("the CLI verifies through the content-addressed cache", () => {
  const SOURCE = `/** @post result === x */\nexport function identity(x: number): number {\n  return x;\n}\n`;

  /** The cache entry the CLI wrote for `path` in strict mode with imports verified. */
  function entryFile(path: string, source: string): string {
    return join(CACHE_DIR, `${cacheKey(path, source, { strict: true, verifyImports: true, solver: isAvailable() })}.json`);
  }

  test("a second run is a hit, editing invalidates, and modes never share entries", () => {
    const path = join(SCRATCH, "cached.ts");
    writeFileSync(path, SOURCE, "utf8");
    const first = cli([path]);
    expect(first.code).toBe(0);

    // Tamper with the cached verdict: only a run that *reads* the cache can be affected.
    const entry = entryFile(path, SOURCE);
    const data = JSON.parse(readFileSync(entry, "utf8")) as { report: { ok: boolean } };
    data.report.ok = false;
    writeFileSync(entry, JSON.stringify(data), "utf8");

    // ... a lenient run has its own key, so it is unaffected.
    const lenient = cli([path, "--lenient"]);
    expect(lenient.code).toBe(0);

    // ... a strict run is a hit and reports the cached (tampered) verdict.
    const hit = cli([path]);
    expect(hit.code).toBe(1);

    // ... `DEP_VERIFY_NO_CACHE=1` bypasses the entry and re-verifies.
    const previous = process.env.DEP_VERIFY_NO_CACHE;
    process.env.DEP_VERIFY_NO_CACHE = "1";
    try {
      expect(cli([path]).code).toBe(0);
    } finally {
      if (previous === undefined) delete process.env.DEP_VERIFY_NO_CACHE;
      else process.env.DEP_VERIFY_NO_CACHE = previous;
    }

    // ... and editing the file changes the key, so the stale verdict cannot be served.
    const edited = SOURCE.replace("result === x", "result === x && x === x");
    writeFileSync(path, edited, "utf8");
    expect(cli([path]).code).toBe(0);
    expect(entryFile(path, edited)).not.toBe(entry);
  });
});
