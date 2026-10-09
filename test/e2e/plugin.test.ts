/**
 * Milestone 8: the plugin under `bun run`, under `DEP_VERIFY_STRICT=1`, and under
 * `Bun.build` (section 9.4).
 *
 * The runtime tests run the example as a *subprocess* (`bun run examples/runtime/main.ts`),
 * because that is the only way to exercise the preload plugin the way a user does.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { resolve } from "node:path";
import { depVerifyPlugin, isOwnSource } from "../../src/plugin";

setDefaultTimeout(300_000);

const repoRoot = resolve(import.meta.dir, "../..");

interface Completed {
  readonly exitCode: number;
  readonly stdout: string;
  readonly stderr: string;
}

/** Every environment variable the plugin reads, pinned for the subprocess. */
function pluginEnv(overrides: Record<string, string> = {}): Record<string, string> {
  return {
    ...process.env,
    NODE_ENV: "development",
    DEP_VERIFY_STRICT: "0",
    ...overrides,
  };
}

function runBun(argv: readonly string[], env: Record<string, string> = {}): Completed {
  const proc = Bun.spawnSync({
    cmd: ["bun", ...argv],
    cwd: repoRoot,
    env: pluginEnv(env),
    stdout: "pipe",
    stderr: "pipe",
  });
  return {
    exitCode: proc.exitCode ?? -1,
    stdout: proc.stdout.toString(),
    stderr: proc.stderr.toString(),
  };
}

/** Run `build` with environment variables set, restoring them afterwards. */
async function withEnv<T>(values: Record<string, string>, build: () => Promise<T>): Promise<T> {
  const previous = new Map<string, string | undefined>();
  for (const [key, value] of Object.entries(values)) {
    previous.set(key, process.env[key]);
    process.env[key] = value;
  }
  try {
    return await build();
  } finally {
    for (const [key, value] of previous) {
      if (value === undefined) delete process.env[key];
      else process.env[key] = value;
    }
  }
}

const CLAMP = resolve(repoRoot, "examples/pass/clamp.ts");
const SAFE_GET = resolve(repoRoot, "examples/pass/safeGet.ts");
const CLAMP_NO_PRE = resolve(repoRoot, "examples/fail/clampNoPre.ts");

describe("the plugin under `bun run`", () => {
  const result = runBun(["run", "examples/runtime/main.ts"]);

  test("throws a PreconditionError for the second, out-of-bounds call", () => {
    expect(result.exitCode).not.toBe(0);
    expect(result.stderr).toContain("PreconditionError");
    expect(result.stderr).toContain('precondition `0 <= i && i < a.length` failed');
    // The first call ran normally, so injection did not change legal behaviour.
    expect(result.stdout).toContain("20");
  });

  test("the stack trace's first frame is safeGet.ts at the function's original line", () => {
    const frames = result.stderr
      .split("\n")
      .filter((line) => /^\s*at\s/.test(line) && /safeGet\.ts:\d+:\d+/.test(line));
    expect(frames.length).toBeGreaterThan(0);
    // `export function safeGet<T>(a: readonly T[], i: number): T {` is line 4 of the file:
    // the injected precondition check is on that line, and no line was added anywhere.
    expect(frames[0]).toMatch(/safeGet\.ts:4:\d+/);
  });
});

describe("the plugin in strict mode", () => {
  const result = runBun(["run", "test/e2e/fixtures/importFailing.ts"], { DEP_VERIFY_STRICT: "1" });

  test("importing a failing example rejects with the diagnostic text", () => {
    expect(result.exitCode).not.toBe(0);
    expect(result.stderr).toContain("error[post]");
    expect(result.stderr).toContain("examples/fail/clampNoPre.ts:5:15");
    expect(result.stderr).toContain("postcondition");
    expect(result.stdout).not.toContain("imported despite strict mode");
  });
});

describe("Bun.build with the plugin", () => {
  test("succeeds for examples/pass", async () => {
    const result = await Bun.build({
      entrypoints: [CLAMP, SAFE_GET],
      plugins: [depVerifyPlugin],
      target: "bun",
    });
    expect(result.success).toBe(true);
    expect(result.logs).toEqual([]);
    const output = (await Promise.all(result.outputs.map((artifact) => artifact.text()))).join("\n");
    // Guards, preconditions, postcondition checks and internal checks are all present.
    expect(output).toContain('guardInt("clamp", "x", x)');
    expect(output).toContain('throw new PreconditionError("clamp", "lo <= hi"');
    expect(output).toContain('"lo <= result && result <= hi"');
    expect(output).toContain("checkIndex(a, i,");
  });

  test("with NODE_ENV=production the output keeps preconditions and guards but drops certified postconditions", async () => {
    const result = await withEnv({ NODE_ENV: "production" }, () =>
      Bun.build({ entrypoints: [CLAMP, SAFE_GET], plugins: [depVerifyPlugin], target: "bun" }),
    );
    expect(result.success).toBe(true);
    const output = (await Promise.all(result.outputs.map((artifact) => artifact.text()))).join("\n");
    // Exported preconditions and boundary guards always stay...
    expect(output).toContain('guardInt("clamp", "x", x)');
    expect(output).toContain('throw new PreconditionError("clamp", "lo <= hi"');
    expect(output).toContain('guardArray("safeGet", "a", a)');
    // ... the certified postcondition check and the certified index check do not.
    expect(output).not.toContain('"lo <= result && result <= hi"');
    expect(output).not.toContain("checkIndex(a, i,");
  });

  test("with throw: false a failing example fails the build with diagnostics in logs", async () => {
    const result = await withEnv({ DEP_VERIFY_STRICT: "1" }, () =>
      Bun.build({ entrypoints: [CLAMP_NO_PRE], plugins: [depVerifyPlugin], target: "bun", throw: false }),
    );
    expect(result.success).toBe(false);
    const logs = result.logs.map((log) => log.message).join("\n");
    expect(logs).toContain("error[post]");
    expect(logs).toContain("clampNoPre.ts:5:15");
  });
});

describe("what the plugin refuses to verify", () => {
  test("this repository's own sources (and tests, and scripts) are skipped", () => {
    expect(isOwnSource(resolve(repoRoot, "src/verify.ts"))).toBe(true);
    expect(isOwnSource(resolve(repoRoot, "src/inject/runtime.ts"))).toBe(true);
    expect(isOwnSource(resolve(repoRoot, "test/e2e/plugin.test.ts"))).toBe(true);
    expect(isOwnSource(resolve(repoRoot, "scripts/setup-z3.ts"))).toBe(true);
    expect(isOwnSource(resolve(repoRoot, "examples/pass/clamp.ts"))).toBe(false);
    expect(isOwnSource("/tmp/elsewhere/clamp.ts")).toBe(false);
  });
});
