/**
 * Plugin regressions: strict mode must verify imported specs (section 6.5), and an
 * already-injected file must not be re-verified (section 6.7).
 *
 * Without the first, `DEP_VERIFY_STRICT=1` under `bun run`/`Bun.build` admitted a caller whose
 * postcondition rested on a *failed* imported spec.  Without the second, the `__dv` runtime
 * import that injection adds was read as user code, and the bogus `error[fragment]: unresolved
 * name __dv` made the file unloadable in strict mode.
 */
import { afterAll, describe, expect, setDefaultTimeout, test } from "bun:test";
import { mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { verifyCached } from "../../src/cache";
import { inject, isInjected } from "../../src/inject/inject";
import { depVerifyPlugin } from "../../src/plugin";
import { verify } from "../../src/verify";

setDefaultTimeout(300_000);

const repoRoot = resolve(import.meta.dir, "../..");
const SCRATCH = join(repoRoot, ".dep-verify", `fixb-plugin-${process.pid}-${Date.now()}`);
mkdirSync(SCRATCH, { recursive: true });
afterAll(() => rmSync(SCRATCH, { recursive: true, force: true }));

/** The plugin's `onLoad` callback, captured from a stand-in builder. */
function loadHandler(): (args: { path: string }) => { contents: string; loader: string } {
  let handler: ((args: { path: string }) => { contents: string; loader: string }) | undefined;
  (depVerifyPlugin.setup as (builder: unknown) => void)({
    onLoad: (_filter: unknown, callback: typeof handler) => {
      handler = callback;
    },
  });
  if (handler === undefined) throw new Error("the plugin registered no onLoad handler");
  return handler;
}

async function withEnv<T>(values: Record<string, string>, body: () => T | Promise<T>): Promise<T> {
  const previous = new Map<string, string | undefined>();
  for (const [key, value] of Object.entries(values)) {
    previous.set(key, process.env[key]);
    process.env[key] = value;
  }
  try {
    return await body();
  } finally {
    for (const [key, value] of previous) {
      if (value === undefined) delete process.env[key];
      else process.env[key] = value;
    }
  }
}

function runBun(argv: readonly string[], env: Record<string, string>): { code: number; stdout: string; stderr: string } {
  const proc = Bun.spawnSync({
    cmd: ["bun", ...argv],
    cwd: repoRoot,
    env: { ...process.env, NODE_ENV: "development", DEP_VERIFY_STRICT: "0", ...env },
    stdout: "pipe",
    stderr: "pipe",
  });
  return {
    code: proc.exitCode ?? -1,
    stdout: proc.stdout.toString(),
    stderr: proc.stderr.toString(),
  };
}

const WEAK_CLAMP = `/**
 * @pre lo <= hi
 * @post lo <= result && result <= hi
 */
export function weakClamp(x: number, lo: number, hi: number): number {
  return x;
}
`;

const CALLER = `import { weakClamp } from "./weakClamp";

/**
 * @post 0 <= result && result <= 100
 */
export function percent(p: number): number {
  return weakClamp(p, 0, 100);
}

console.log("percent(-100) =", percent(-100));
`;

function writeAdmissionCase(): { caller: string; weakClamp: string } {
  const caller = join(SCRATCH, "caller.ts");
  const weakClamp = join(SCRATCH, "weakClamp.ts");
  writeFileSync(weakClamp, WEAK_CLAMP, "utf8");
  writeFileSync(caller, CALLER, "utf8");
  return { caller, weakClamp };
}

describe("strict mode verifies imported specs", () => {
  test("verifyCached({strict:true}) marks a caller of a failed import", () => {
    const { caller } = writeAdmissionCase();
    // What the plugin used to do: imports unverified, the caller looks certified.
    const shallow = verifyCached(caller, CALLER, { strict: true, verifyImports: false, cacheDir: join(SCRATCH, "c1") });
    expect(shallow.ok).toBe(true);
    expect(shallow.functions[0]!.dependsOnUncertified).toEqual([]);

    const strict = verifyCached(caller, CALLER, { strict: true, cacheDir: join(SCRATCH, "c2") });
    expect(strict.ok).toBe(false);
    expect(strict.externals[0]!.certified).toBe(false);
    expect(strict.functions[0]!.dependsOnUncertified).toContain("weakClamp");
  });

  test("`bun run` in strict mode refuses to load such a caller", () => {
    const { caller } = writeAdmissionCase();
    const result = runBun(["run", caller], { DEP_VERIFY_STRICT: "1" });
    expect(result.code).not.toBe(0);
    expect(result.stderr).toContain("strict verification failed");
    expect(result.stderr).toContain("weakClamp");
    expect(result.stdout).not.toContain("percent(-100)");
  });

  test("Bun.build in strict mode fails the build, with the reason in the logs", async () => {
    const { caller } = writeAdmissionCase();
    const result = await withEnv({ DEP_VERIFY_STRICT: "1" }, () =>
      Bun.build({ entrypoints: [caller], plugins: [depVerifyPlugin], target: "bun", throw: false }),
    );
    expect(result.success).toBe(false);
    expect(result.logs.map((log) => log.message).join("\n")).toContain("weakClamp");
  });

  test("a certified import passes strict mode unchanged", () => {
    const result = runBun(["run", "examples/runtime/main.ts"], { DEP_VERIFY_STRICT: "1" });
    // The example still runs to its (expected) PreconditionError, not to a strict failure.
    expect(result.stderr).toContain("PreconditionError");
    expect(result.stderr).not.toContain("strict verification failed");
  });
});

describe("an already-injected file is not re-verified", () => {
  test("the plugin returns it unchanged, with loader `ts`", async () => {
    const path = join(SCRATCH, "injected.ts");
    const source = `${readFileSync(join(repoRoot, "examples/pass/clamp.ts"), "utf8")}
console.log("clamp(5, 0, 10) =", clamp(5, 0, 10));
`;
    const report = verifyCached(path, source, { cacheDir: join(SCRATCH, "c3") });
    const injected = inject(source, report.plan, { path });
    expect(isInjected(injected)).toBe(true);
    writeFileSync(path, injected, "utf8");

    // What re-verification would report: the runtime import is user code to the fragment
    // checker, so the file would be rejected (and unloadable in strict mode).
    const reverified = verify(path, injected, { solver: false });
    expect(reverified.functions.map((fn) => `${fn.name}:${fn.status}`)).toEqual(["clamp:rejected"]);
    expect(reverified.diagnostics.some((d) => d.message.includes("`__dv`"))).toBe(true);

    const loaded = await withEnv({ DEP_VERIFY_STRICT: "1" }, () => loadHandler()({ path }));
    expect(loaded.contents).toBe(injected);
    expect(loaded.loader).toBe("ts");

    // ... and it still runs under `bun run` in strict mode.
    const executed = runBun(["run", path], { DEP_VERIFY_STRICT: "1" });
    expect(executed.code).toBe(0);
    expect(executed.stdout).toContain("clamp(5, 0, 10) = 5");
  });

  test("a file that merely imports the runtime module by hand is skipped too", () => {
    const path = join(SCRATCH, "manual.ts");
    const source = `import * as __dv from "${resolve(repoRoot, "src/inject/runtime.ts")}";

/**
 * @pre lo <= hi
 * @post lo <= result && result <= hi
 */
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
`;
    writeFileSync(path, source, "utf8");
    const loaded = loadHandler()({ path });
    expect(loaded.contents).toBe(source);
  });
});
