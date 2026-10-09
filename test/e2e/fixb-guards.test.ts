/**
 * Boundary guards and retained preconditions for functions reachable from unverified code.
 *
 * A non-exported verified function called from unverified code in the same file gets boundary
 * guards, because its kernel type assumes `InRange` for its `number` parameters (section 6.6).
 * "Reachable" has to be read conservatively: `export { f };` makes `f` callable from outside
 * the module, and `const alias = used;` reaches `used` without ever writing `used(`.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { inject } from "../../src/inject/inject";
import { parseFile } from "../../src/syntax/parser";
import { verify } from "../../src/verify";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");

function verifySource(label: string, source: string) {
  const path = `/tmp/fixb-guards/${label}.ts`;
  return { path, source, result: verify(path, source, { solver: false }) };
}

function guardsOf(result: ReturnType<typeof verify>): string[] {
  return result.plan
    .filter((record) => record.isBoundaryGuard)
    .map((record) => `${record.function}.${record.param}:${record.exported}`);
}

const HELPER = `/**
 * @pre x >= 0
 * @post result >= 0
 */
function helper(x: number): number {
  return x;
}
`;

describe("guards for functions unverified code can reach", () => {
  test("a non-exported function called from unverified code gets a guard", () => {
    const { path, source, result } = verifySource("called", `${HELPER}
console.log(helper(3));
`);
    expect(guardsOf(result)).toEqual(["helper.x:false"]);
    const development = inject(source, result.plan, { path });
    expect(development).toContain('guardInt("helper", "x", x)');
    const production = inject(source, result.plan, { path, production: true });
    expect(production).toContain('guardInt("helper", "x", x)');
    expect(production).toContain('PreconditionError("helper"');
  });

  test("a non-exported function called only from verified code gets no guard", () => {
    const { result } = verifySource(
      "internal",
      `${HELPER}
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function caller(x: number): number {
  return helper(x);
}
`,
    );
    expect(guardsOf(result)).toEqual(["caller.x:true"]);
  });

  test("`export { f };` makes `f` exported even though its declaration is not", () => {
    const source = `${HELPER}
export { helper };
`;
    const parsed = parseFile("export-list.ts", source);
    expect(parsed.functions.map((fn) => `${fn.name}:${fn.exported}`)).toEqual(["helper:true"]);
    const { path, result } = verifySource("export-list", source);
    // The cross-check must still agree with Bun: the printed declaration has no `export`.
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
    expect(guardsOf(result)).toEqual(["helper.x:true"]);
    const production = inject(source, result.plan, { path, production: true });
    expect(production).toContain('guardInt("helper", "x", x)');
    expect(production).toContain('PreconditionError("helper"');
  });

  test("`export { f as g };` and `export default function f` count too", () => {
    const renamed = `${HELPER}
export { helper as g };
`;
    expect(parseFile("renamed.ts", renamed).functions[0]!.exported).toBe(true);
    expect(guardsOf(verifySource("renamed", renamed).result)).toEqual(["helper.x:true"]);

    const defaulted = `/**
 * @pre x >= 0
 * @post result >= 0
 */
export default function helper(x: number): number {
  return x;
}
`;
    const parsed = parseFile("default.ts", defaulted);
    expect(parsed.functions[0]!.exported).toBe(true);
    const { result } = verifySource("default", defaulted);
    // `export default` normalises differently from `export`, so the cross-check would fail
    // if the printer dropped the `default` keyword.
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
    expect(guardsOf(result)).toEqual(["helper.x:true"]);
  });

  test("a re-export (`export { x } from …`) does not mark a local function", () => {
    const source = `${HELPER}
export { something } from "./other";
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function caller(x: number): number {
  return helper(x);
}
`;
    expect(parseFile("re-export.ts", source).functions.map((fn) => fn.exported)).toEqual([false, true]);
    expect(guardsOf(verifySource("re-export", source).result)).toEqual(["caller.x:true"]);
  });

  test("an alias of a non-exported function is a reference from unverified code", () => {
    const source = `/**
 * @pre x >= 0
 * @post result >= 0
 */
function used(x: number): number {
  return x;
}

const alias = used;

export function callAlias(x: number): number {
  return alias(x);
}
`;
    const { path, result } = verifySource("alias", source);
    expect(result.diagnostics.filter((d) => d.kind === "internal")).toEqual([]);
    // `callAlias` has no spec, so both the call through `alias` and the bare `used` mention
    // reach `used`.
    expect(guardsOf(result)).toContain("used.x:false");
    const production = inject(source, result.plan, { path, production: true });
    expect(production).toContain('guardInt("used", "x", x)');
    expect(production).toContain('PreconditionError("used"');
  });

  test("a mention that cannot call anything is still kept (conservative)", () => {
    // `names` holds the name but nothing calls it: keeping the check is harmless, dropping
    // one is not.
    const source = `${HELPER}
const table = { helper };
export function caller(x: number): number {
  return table.helper(x);
}
`;
    const result = verifySource("mention", source).result;
    expect(guardsOf(result)).toContain("helper.x:false");
  });
});

describe("production behaviour of the reachable cases", () => {
  test("a bad argument still throws in production, for both shapes", () => {
    const dir = join(repoRoot, ".dep-verify", `fixb-guards-${process.pid}-${Date.now()}`);
    mkdirSync(dir, { recursive: true });
    writeFileSync(
      join(dir, "s_export_list.ts"),
      `${HELPER}
export { helper };
`,
      "utf8",
    );
    writeFileSync(
      join(dir, "s_alias.ts"),
      `/**
 * @pre x >= 0
 * @post result >= 0
 */
function used(x: number): number {
  return x;
}

const alias = used;

export function callAlias(x: number): number {
  return alias(x);
}
`,
      "utf8",
    );
    writeFileSync(
      join(dir, "main.ts"),
      `import { helper } from "./s_export_list";
import { callAlias } from "./s_alias";

function attempt(label: string, thunk: () => unknown): void {
  try {
    console.log(\`\${label} -> \${JSON.stringify(thunk())} (NO ERROR)\`);
  } catch (error) {
    console.log(\`\${label} -> \${(error as Error).name}\`);
  }
}

attempt("helper(-1)", () => helper(-1));
attempt("callAlias(-1)", () => callAlias(-1));
`,
      "utf8",
    );
    const run = (nodeEnv: string): { code: number; stdout: string } => {
      const proc = Bun.spawnSync({
        cmd: ["bun", "run", join(dir, "main.ts")],
        cwd: repoRoot,
        env: { ...process.env, NODE_ENV: nodeEnv, DEP_VERIFY_STRICT: "0" },
        stdout: "pipe",
        stderr: "pipe",
      });
      return { code: proc.exitCode ?? -1, stdout: proc.stdout.toString() };
    };
    try {
      const development = run("development");
      const production = run("production");
      for (const [label, result] of [
        ["development", development],
        ["production", production],
      ] as const) {
        expect(`${label}: ${result.stdout}`).toContain("helper(-1) -> PreconditionError");
        expect(`${label}: ${result.stdout}`).toContain("callAlias(-1) -> PreconditionError");
        expect(`${label}: ${result.stdout}`).not.toContain("NO ERROR");
        expect(result.code).toBe(0);
      }
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
