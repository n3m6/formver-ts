/**
 * Milestone 8: the CLI as a subprocess (specification 4.4 and section 9.4).
 *
 * The CLI is run the way a user runs it — `bun run verify …` — so these tests cover the
 * package.json script, the argument handling, the exit codes, the summary table and the
 * "libz3 is missing" rule.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { contentHash } from "../../src/extract/specs";

// One run verifies every example; `binarySearch`'s loop obligations are seconds of Z3.
setDefaultTimeout(300_000);

const repoRoot = resolve(import.meta.dir, "../..");

interface Completed {
  readonly exitCode: number;
  readonly stdout: string;
  readonly stderr: string;
}

function cli(argv: readonly string[], env: Record<string, string> = {}): Completed {
  const proc = Bun.spawnSync({
    cmd: ["bun", ...argv],
    cwd: repoRoot,
    env: { ...process.env, ...env },
    stdout: "pipe",
    stderr: "pipe",
  });
  return {
    exitCode: proc.exitCode ?? -1,
    stdout: proc.stdout.toString(),
    stderr: proc.stderr.toString(),
  };
}

/** `bun run verify …`, exactly as the README documents it. */
function verify(args: readonly string[] = [], env: Record<string, string> = {}): Completed {
  return cli(["run", "verify", ...args], env);
}

/** Captured before any CLI run, so the "does not inject" test compares against the original. */
const clampPath = resolve(repoRoot, "examples/pass/clamp.ts");
const clampText = readFileSync(clampPath, "utf8");

const PASS_FILES = [
  "abs.ts",
  "binarySearch.ts",
  "clamp.ts",
  "concat.ts",
  "safeGet.ts",
  "shape.ts",
  "sumTo.ts",
  "take.ts",
  "useClamp.ts",
];

describe("bun run verify examples/pass", () => {
  const result = verify(["examples/pass"]);

  test("exits 0 with every function certified and zero axioms", () => {
    // `bun run <script>` echoes the command it ran; the only other stderr output would be an
    // error.
    expect(result.stderr).not.toContain("error:");
    expect(result.exitCode).toBe(0);
    expect(result.stdout).not.toContain("error[");
    for (const file of PASS_FILES) {
      // Every per-file row shows one certified function and nothing else.
      expect(result.stdout).toMatch(
        new RegExp(`examples/pass/${file.replace(".", "\\.")}\\s+1\\s+0\\s+0\\s+0`),
      );
    }
    expect(result.stdout).toMatch(/total\s+9\s+0\s+0\s+0/);
    expect(result.stdout).toContain("axioms used: 0");
    expect(result.stdout).toContain("9 file(s) verified");
  });

  test("does not inject into the code it verifies", () => {
    expect(clampText).not.toContain("__dv.");
    expect(contentHash(readFileSync(clampPath, "utf8"))).toBe(contentHash(clampText));
  });
});

describe("bun run verify examples/fail", () => {
  const result = verify(["examples/fail"]);

  test("exits 1 with each expected diagnostic kind and location", () => {
    expect(result.exitCode).toBe(1);
    const out = result.stdout;
    // error[post] at the postcondition sites
    expect(out).toMatch(/examples\/fail\/clampNoPre\.ts:5:15: error\[post\]/);
    expect(out).toMatch(/examples\/fail\/clampNoPre\.ts:6:15: error\[post\]/);
    // error[index] at `a[i]`
    expect(out).toMatch(/examples\/fail\/offByOne\.ts:5:10: error\[index\]/);
    // error[range] at `x + y`, and the postcondition that mentions it
    expect(out).toMatch(/examples\/fail\/overflow\.ts:5:10: error\[range\]/);
    expect(out).toMatch(/examples\/fail\/overflow\.ts:5:3: error\[post\]/);
    // error[measure-decrease] at the recursive call
    expect(out).toMatch(/examples\/fail\/noDecrease\.ts:7:10: error\[measure-decrease\]/);
    // one error[fragment] per rejected construct
    const fragment = out.match(/error\[fragment\]/g) ?? [];
    expect(fragment.length).toBeGreaterThanOrEqual(8);
    expect(out).toMatch(/examples\/fail\/rejected\.ts:11:33: error\[fragment\]/);
    expect(out).toMatch(/examples\/fail\/rejected\.ts:20:10: error\[fragment\]/);
    // The summary counts the failed and rejected functions, and still no axioms.
    expect(out).toMatch(/total\s+0\s+0\s+4\s+8/);
    expect(out).toContain("axioms used: 0");
  });

  test("reports a counterexample with every failing obligation", () => {
    expect(result.stdout).toContain("counterexample:");
  });
});

describe("external declarations (section 6.1.5)", () => {
  const fixture = "test/e2e/fixtures/callUncertified.ts";

  test("strict mode fails an imported declaration that is not certified in its own file", () => {
    const result = cli(["src/cli.ts", fixture]);
    expect(result.exitCode).toBe(1);
    expect(result.stdout).toContain("error[uncertified]");
    expect(result.stdout).toContain("the imported declaration `badAdd` is not certified");
    expect(result.stdout).toContain("callUncertified.ts:1:1");
  });

  test("lenient mode warns instead", () => {
    const result = cli(["src/cli.ts", fixture, "--lenient"]);
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toContain("warning[uncertified]");
    expect(result.stdout).toContain("badAdd");
  });
});

describe("the default path", () => {
  test("`bun run verify` verifies examples/pass", () => {
    const result = verify();
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toContain("examples/pass/clamp.ts");
    expect(result.stdout).toMatch(/total\s+9\s+0\s+0\s+0/);
  });
});

describe("libz3 is missing (section 4.4)", () => {
  const env = { DEP_VERIFY_LIBZ3: "/nonexistent/libz3.so" };

  test("strict mode errors out", () => {
    const result = verify(["examples/pass"], env);
    expect(result.exitCode).toBe(1);
    expect(result.stderr).toContain("libz3");
    expect(result.stderr).toContain("strict mode needs Z3");
  });

  test("lenient mode warns once and runtime-checks every obligation", () => {
    const result = verify(["examples/pass", "--lenient"], env);
    expect(result.exitCode).toBe(0);
    // Exactly one warning about the missing library, and one about the consequence.
    const warnings = result.stderr.split("\n").filter((line) => line.startsWith("warning:"));
    expect(warnings.length).toBe(2);
    expect(warnings[0]).toContain("libz3");
    expect(warnings[1]).toContain("runtime-checked");
    // Every function is "smt-only": not discharged, so a runtime check is needed.
    expect(result.stdout).toMatch(/total\s+0\s+9\s+0\s+0/);
    expect(result.stdout).toContain("note: no SMT solver available");
    expect(result.stdout).not.toContain("error[");
  });
});

describe("usage", () => {
  test("an unknown option is a usage error (exit 2)", () => {
    const result = cli(["src/cli.ts", "--wat"]);
    expect(result.exitCode).toBe(2);
    expect(result.stderr).toContain("usage: bun run verify");
  });

  test("--help prints the usage and exits 0", () => {
    const result = cli(["src/cli.ts", "--help"]);
    expect(result.exitCode).toBe(0);
    expect(result.stdout).toContain("usage: bun run verify");
  });

  test("a missing path fails", () => {
    const result = cli(["src/cli.ts", "examples/nope"]);
    expect(result.exitCode).toBe(1);
    expect(result.stderr).toContain("no such file or directory");
  });
});
