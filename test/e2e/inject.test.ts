/**
 * Milestone 8, injection unit tests (specification 6.6).
 *
 * Everything here is about the *text* injection produces: no line is added or removed, no
 * newline is ever inserted, the original source survives as a subsequence, the guards and
 * `@pre`/`@post` checks appear where the plan says, and production strips exactly the checks
 * the table allows it to strip.  The runtime behaviour of the injected code is the plugin
 * test's job (`test/e2e/plugin.test.ts`).
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { offsetToPosition, type Span } from "../../src/diagnostics";
import { InjectionError, inject } from "../../src/inject/inject";
import * as runtime from "../../src/inject/runtime";
import { verify, type InjectionRecord } from "../../src/verify";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");
const RUNTIME = "/tmp/dep-verify-runtime.ts";

function read(relative: string): string {
  return readFileSync(resolve(repoRoot, relative), "utf8");
}

/** Verify an example and return its path, source and result. */
function run(relative: string): { path: string; source: string; plan: InjectionRecord[] } {
  const path = resolve(repoRoot, relative);
  const source = readFileSync(path, "utf8");
  const result = verify(path, source, {});
  return { path, source, plan: [...result.plan] };
}

/** A span covering the `occurrence`-th (0-based) appearance of `needle`. */
function spanAt(source: string, needle: string, file = "test.ts", occurrence = 0): Span {
  let offset = -1;
  let from = 0;
  for (let i = 0; i <= occurrence; i += 1) {
    offset = source.indexOf(needle, from);
    if (offset < 0) throw new Error(`the test source does not contain ${JSON.stringify(needle)}`);
    from = offset + 1;
  }
  const { line, col } = offsetToPosition(source, offset);
  return { file, line, col, offset, endOffset: offset + needle.length };
}

function record(partial: Partial<InjectionRecord> & Pick<InjectionRecord, "function" | "kind" | "span" | "specText">): InjectionRecord {
  return {
    exported: true,
    certified: false,
    isPrecondition: false,
    isBoundaryGuard: false,
    ...partial,
  };
}

function lineCount(text: string): number {
  return text.split("\n").length;
}

/** True when every character of `needle` appears in `haystack` in order. */
function isSubsequence(needle: string, haystack: string): boolean {
  let at = 0;
  for (const character of haystack) {
    if (at < needle.length && needle[at] === character) at += 1;
  }
  return at === needle.length;
}

const INJECTABLE = ["clamp", "abs", "safeGet", "take", "concat", "useClamp", "shape", "sumTo"] as const;

describe("injection never changes the line structure", () => {
  for (const name of INJECTABLE) {
    test(`examples/pass/${name}.ts: only insertions, same line count`, () => {
      const { path, source, plan } = run(`examples/pass/${name}.ts`);
      expect(plan.length).toBeGreaterThan(0);
      for (const production of [false, true]) {
        const injected = inject(source, plan, { path, production, runtimePath: RUNTIME });
        expect(injected).not.toBe(source);
        expect(lineCount(injected)).toBe(lineCount(source));
        // Insertions only: the original text is a subsequence of the output.
        expect(isSubsequence(source, injected)).toBe(true);
        // ... and Bun still parses the result (inject checks this itself as well).
        new Bun.Transpiler({ loader: "ts" }).transformSync(injected);
      }
    });
  }

  test("every output line is its original line with text inserted only", () => {
    for (const name of INJECTABLE) {
      const { path, source, plan } = run(`examples/pass/${name}.ts`);
      const injected = inject(source, plan, { path, runtimePath: RUNTIME });
      const originalLines = source.split("\n");
      const injectedLines = injected.split("\n");
      expect(injectedLines.length).toBe(originalLines.length);
      for (let i = 0; i < originalLines.length; i += 1) {
        expect(isSubsequence(originalLines[i]!, injectedLines[i]!)).toBe(true);
      }
    }
  });

  test("injection is idempotent: an injected file is left alone", () => {
    const { path, source, plan } = run("examples/pass/clamp.ts");
    const once = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(inject(once, plan, { path, runtimePath: RUNTIME })).toBe(once);
  });

  test("a `#!` shebang keeps line 1: the runtime import goes on line 2", () => {
    const source = [
      "#!/usr/bin/env bun",
      "/**",
      " * @post result >= 0",
      " */",
      "export function abs(x: number): number { return x < 0 ? -x : x; }",
      "",
    ].join("\n");
    const plan = [
      record({
        function: "abs",
        kind: "post",
        span: spanAt(source, "@post result >= 0"),
        specText: "result >= 0",
      }),
    ];
    const injected = inject(source, plan, { path: "shebang.ts", runtimePath: RUNTIME });
    const lines = injected.split("\n");
    expect(lines[0]).toBe("#!/usr/bin/env bun");
    expect(lines[1]!.startsWith(`import * as __dv from ${JSON.stringify(RUNTIME)};`)).toBe(true);
    expect(lineCount(injected)).toBe(lineCount(source));
  });
});

describe("what the checks look like", () => {
  test("clamp: guards, the precondition, and a wrapped return per postcondition", () => {
    const { path, source, plan } = run("examples/pass/clamp.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain('__dv.guardInt("clamp", "x", x)');
    expect(injected).toContain('__dv.guardInt("clamp", "lo", lo)');
    expect(injected).toContain('__dv.guardInt("clamp", "hi", hi)');
    expect(injected).toContain('if (!(lo <= hi)) throw new __dv.PreconditionError("clamp", "lo <= hi", {x, lo, hi}');
    expect(injected).toContain('throw new __dv.PostconditionError("clamp", "lo <= result && result <= hi", {x, lo, hi, result}');
    // One postcondition check per `return`, including the two early ones.
    expect(injected.match(/PostconditionError/g)!.length).toBe(3);
    // Spec expressions are inserted as written, so the source text survives.
    expect(injected).toContain("lo <= result && result <= hi");
  });

  test("safeGet: the index check wraps the index expression", () => {
    const { path, source, plan } = run("examples/pass/safeGet.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain("a[__dv.checkIndex(a, i, ");
    expect(injected).toContain('__dv.guardArray("safeGet", "a", a)');
  });

  test("take: the slice check is appended to the call's arguments", () => {
    const { path, source, plan } = run("examples/pass/take.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain("a.slice(0, n, __dv.checkSlice(a, 0, n, ");
  });

  test("shape: a parenthesised sub-expression is widened before it is wrapped", () => {
    const { path, source, plan } = run("examples/pass/shape.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain("__dv.checkRange(2 * (__dv.checkRange(s.w + s.h, ");
  });

  test("useClamp: the imported callee's precondition is substituted with the call's arguments", () => {
    const { path, source, plan } = run("examples/pass/useClamp.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain('__dv.checkPre(((0) <= (100)), "clamp", "lo <= hi"');
  });

  test("sumTo: a recursive call's measure obligations are checked in place", () => {
    const { path, source, plan } = run("examples/pass/sumTo.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME });
    expect(injected).toContain('__dv.checkMeasure(((n - 1)), "sumTo", "@decreases n"');
    expect(injected).toContain("__dv.checkCallMeasureDecrease(((n - 1)), (n), ");
    expect(injected).toContain('__dv.checkPre((0 <= (n - 1) && (n - 1) <= 1000000), "sumTo"');
  });
});

describe("production stripping", () => {
  test("a certified postcondition is dropped; an uncertified one stays", () => {
    const certified = run("examples/pass/clamp.ts");
    const production = inject(certified.source, certified.plan, {
      path: certified.path,
      production: true,
      runtimePath: RUNTIME,
    });
    expect(production).toContain("__dv.PreconditionError");
    expect(production).toContain("__dv.guardInt");
    expect(production).not.toContain("__dv.PostconditionError");

    const failing = run("examples/fail/clampNoPre.ts");
    const failingProduction = inject(failing.source, failing.plan, {
      path: failing.path,
      production: true,
      runtimePath: RUNTIME,
    });
    expect(failingProduction).toContain("__dv.PostconditionError");
  });

  test("a certified internal check is dropped; an uncertified one stays", () => {
    const safe = run("examples/pass/safeGet.ts");
    expect(safe.plan.some((entry) => entry.kind === "index" && entry.certified)).toBe(true);
    expect(inject(safe.source, safe.plan, { path: safe.path, runtimePath: RUNTIME })).toContain("__dv.checkIndex");
    expect(
      inject(safe.source, safe.plan, { path: safe.path, production: true, runtimePath: RUNTIME }),
    ).not.toContain("__dv.checkIndex");

    const offByOne = run("examples/fail/offByOne.ts");
    expect(offByOne.plan.some((entry) => entry.kind === "index" && !entry.certified)).toBe(true);
    expect(
      inject(offByOne.source, offByOne.plan, { path: offByOne.path, production: true, runtimePath: RUNTIME }),
    ).toContain("__dv.checkIndex");
  });

  test("a non-exported function's precondition stays only when unverified code calls it", () => {
    const source = [
      "/** @pre x >= 0 */",
      "function used(x: number): number { return x; }",
      "/** @pre x >= 0 */",
      "function unused(x: number): number { return x; }",
      "export function caller(x: number): number { return used(x); }",
      "",
    ].join("\n");
    const plan = [
      record({
        function: "used",
        exported: false,
        kind: "pre",
        span: spanAt(source, "@pre x >= 0"),
        specText: "x >= 0",
        isPrecondition: true,
      }),
      record({
        function: "unused",
        exported: false,
        kind: "pre",
        span: spanAt(source, "@pre x >= 0", "test.ts", 1),
        specText: "x >= 0",
        isPrecondition: true,
      }),
    ];
    const development = inject(source, plan, { path: "local.ts", runtimePath: RUNTIME });
    expect(development).toContain('PreconditionError("used"');
    expect(development).toContain('PreconditionError("unused"');
    const production = inject(source, plan, { path: "local.ts", production: true, runtimePath: RUNTIME });
    expect(production).toContain('PreconditionError("used"');
    expect(production).not.toContain('PreconditionError("unused"');
  });

  test("boundary guards are always kept", () => {
    const failing = run("examples/fail/clampNoPre.ts");
    const production = inject(failing.source, failing.plan, {
      path: failing.path,
      production: true,
      runtimePath: RUNTIME,
    });
    expect(production).toContain('__dv.guardInt("clamp", "x", x)');
    expect(production).toContain('__dv.guardInt("clamp", "lo", lo)');
    expect(production).toContain('__dv.guardInt("clamp", "hi", hi)');
  });

  test("a `readonly number[]` parameter gets the O(n) element guard", () => {
    const { path, source, plan } = run("examples/pass/binarySearch.ts");
    const injected = inject(source, plan, { path, runtimePath: RUNTIME, production: true });
    expect(injected).toContain('__dv.guardIntArray("binarySearch", "a", a)');
    expect(injected).toContain('__dv.guardInt("binarySearch", "target", target)');
  });
});

describe("failing loudly", () => {
  test("an edit that cannot be placed is a located internal diagnostic", () => {
    const source = "/** @post result >= 0 */\nexport function f(x: number): number { return x; }\n";
    const plan = [
      record({
        function: "f",
        kind: "index",
        span: spanAt(source, "return x"),
        specText: "0 <= i && i < n",
        siteId: 1,
      }),
    ];
    let thrown: unknown;
    try {
      inject(source, plan, { path: "bad.ts", runtimePath: RUNTIME });
    } catch (error) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(InjectionError);
    const error = thrown as InjectionError;
    expect(error.diagnostic.kind).toBe("internal");
    expect(error.diagnostic.severity).toBe("error");
    expect(error.diagnostic.span.line).toBe(2);
    expect(error.message).toContain("error[internal]");
    expect(error.message).toContain("test.ts:2:");
  });

  test("a plan for a function the file does not declare is rejected, not ignored", () => {
    const source = "/** @post result >= 0 */\nexport function f(x: number): number { return x; }\n";
    const plan = [record({ function: "g", kind: "post", span: spanAt(source, "@post result >= 0"), specText: "result >= 0" })];
    expect(() => inject(source, plan, { path: "bad.ts", runtimePath: RUNTIME })).toThrow(InjectionError);
  });
});

describe("the runtime module", () => {
  test("exports the three error classes and every helper the injection calls", () => {
    const module = runtime as unknown as Record<string, unknown>;
    for (const name of [
      "PreconditionError",
      "PostconditionError",
      "ObligationError",
      "guardInt",
      "guardIntArray",
      "guardArray",
      "guardUnion",
      "checkIndex",
      "checkRange",
      "checkSlice",
      "checkInvariant",
      "checkMeasure",
      "checkLength",
      "checkPre",
    ]) {
      expect(typeof module[name]).not.toBe("undefined");
    }
  });

  test("the errors carry the function, the spec text, the arguments and the location", () => {
    const error = new runtime.PreconditionError("clamp", "lo <= hi", { x: 1, lo: 2, hi: 1 }, "examples/pass/clamp.ts:2:4");
    expect(error.name).toBe("PreconditionError");
    expect(error.fn).toBe("clamp");
    expect(error.spec).toBe("lo <= hi");
    expect(error.args).toEqual({ x: 1, lo: 2, hi: 1 });
    expect(error.file).toBe("examples/pass/clamp.ts");
    expect(error.line).toBe(2);
    expect(error.col).toBe(4);
    expect(error.message).toContain("clamp");
    expect(error.message).toContain("lo <= hi");
    expect(error.message).toContain("examples/pass/clamp.ts:2:4");
    expect(error.message).toContain("x = 1");
    const obligation = new runtime.ObligationError("index", "", "0 <= i && i < a.length", { i: 3 }, "f.ts:1:1");
    expect(obligation.name).toBe("ObligationError");
    expect(obligation.kind).toBe("index");
    expect(obligation.message).toContain("index check");
  });

  test("checks return their value so they can wrap an expression in place", () => {
    expect(runtime.checkIndex([1, 2, 3], 1, "f.ts:1:1")).toBe(1);
    expect(runtime.checkRange(4, "f.ts:1:1")).toBe(4);
    expect(runtime.checkSlice([1, 2, 3], 0, 2, "f.ts:1:1")).toEqual([0, 2]);
    expect(runtime.checkLength([1, 2], "f.ts:1:1")).toEqual([1, 2]);
    expect(runtime.guardInt("f", "x", 3)).toBe(3);
    expect(runtime.guardArray("f", "a", [1, "two"])).toEqual([1, "two"]);
    expect(runtime.checkInvariant(true, "f", "true", "f.ts:1:1")).toBe(true);
    expect(runtime.checkMeasure(2, "f", "n", "f.ts:1:1")).toBe(2);
    expect(runtime.checkPre(true, "f", "0 <= x", "f.ts:1:1")).toBe(true);
    expect(() => runtime.checkIndex([1], 3, "f.ts:1:1")).toThrow(runtime.ObligationError);
    expect(() => runtime.checkRange(1.5, "f.ts:1:1")).toThrow(runtime.ObligationError);
    expect(() => runtime.guardInt("f", "x", 1.5)).toThrow(runtime.ObligationError);
    expect(() => runtime.guardIntArray("f", "a", [1, 2.5])).toThrow(runtime.ObligationError);
    expect(() => runtime.checkInvariant(false, "f", "inv", "f.ts:1:1")).toThrow(runtime.ObligationError);
  });
});
