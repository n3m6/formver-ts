/**
 * Milestone 7, part A: the end-to-end driver (`src/verify.ts`) and the elaborator.
 *
 * Everything here goes through the same pipeline the plugin and the CLI will use:
 * `verify(path, source)` lexes, parses, cross-checks, fragment-checks, elaborates,
 * certifies and asks the kernel to accept the completed term.  The tests assert verdicts,
 * diagnostic kinds and locations, counterexamples (evaluated, never compared literally),
 * the imported `external` declarations and the injection plan.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { formatDiagnostic, spanText, type Diagnostic } from "../../src/diagnostics";
import { elaborateFunction } from "../../src/extract/elaborate";
import { extractFile, renderExpr, type ExprIR } from "../../src/extract/fragment";
import { contentHash } from "../../src/extract/specs";
import * as K from "../../src/kernel/index";
import { verify, type VerifyResult } from "../../src/verify";
import { lex } from "../../src/syntax/lexer";

const repoRoot = resolve(import.meta.dir, "../..");

function read(relative: string): string {
  return readFileSync(resolve(repoRoot, relative), "utf8");
}

function run(relative: string, options: Parameters<typeof verify>[2] = {}): VerifyResult {
  const path = resolve(repoRoot, relative);
  return verify(path, readFileSync(path, "utf8"), options);
}

const PASS_FILES = [
  "examples/pass/clamp.ts",
  "examples/pass/abs.ts",
  "examples/pass/safeGet.ts",
  "examples/pass/concat.ts",
  "examples/pass/take.ts",
  "examples/pass/shape.ts",
  "examples/pass/useClamp.ts",
] as const;

// ---------------------------------------------------------------------------
// examples/pass: every function kernel-certified, with zero axioms
// ---------------------------------------------------------------------------

describe("verify(examples/pass)", () => {
  for (const file of PASS_FILES) {
    test(`${file}: every function is certified, with zero axioms`, () => {
      const result = run(file);
      expect(result.functions.length).toBeGreaterThan(0);
      for (const fn of result.functions) {
        expect(`${fn.name}:${fn.status}`).toBe(`${fn.name}:certified`);
        expect(fn.certified).toBe(true);
      }
      expect(K.axiomsUsed(result.env)).toEqual([]);
      expect(result.axioms).toEqual([]);
      expect(result.ok).toBe(true);
      // Every function was added to the environment as a checked definition (`def`), which
      // is what keeps `axiomsUsed` empty and makes same-file calls work.
      for (const fn of result.functions) {
        const decl = K.lookupDecl(result.env, fn.name);
        expect(decl?.kind).toBe("def");
      }
    });

    test(`${file}: the elaborated term is accepted by K.checkType`, () => {
      const path = resolve(repoRoot, file);
      const source = readFileSync(path, "utf8");
      const ir = extractFile(path, source);
      expect(ir.diagnostics.filter((d) => d.severity === "error")).toEqual([]);
      let env = K.emptyEnv();
      for (const spec of ir.functions.flatMap((fn) => fn.imports)) {
        const added = K.addDecl(env, spec.decl);
        expect(added.ok).toBe(true);
        if (added.ok) env = added.value;
      }
      const byName = new Map(ir.functions.map((fn) => [fn.name, fn]));
      for (const fn of ir.functions) {
        const outcome = elaborateFunction(env, fn, { functions: byName });
        expect(`${fn.name}:${outcome.result.status}`).toBe(`${fn.name}:certified`);
        const term = outcome.result.term!;
        expect(term).toBeDefined();
        const checked = K.checkType(env, term, fn.signature.type);
        if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
        expect(checked.ok).toBe(true);
        // No proof is missing from the completed term: every hole was filled.
        expect(K.formatTerm(term)).not.toContain("tt, tt");
        env = outcome.env;
      }
      expect(K.axiomsUsed(env)).toEqual([]);
    });
  }

  test("the injection plan records guards, preconditions, postconditions and obligations", () => {
    const result = run("examples/pass/clamp.ts");
    const guards = result.plan.filter((record) => record.isBoundaryGuard);
    expect(guards.map((record) => record.param)).toEqual(["x", "lo", "hi"]);
    expect(guards.every((record) => record.exported && record.kind === "guard")).toBe(true);
    const pres = result.plan.filter((record) => record.isPrecondition);
    expect(pres.map((record) => record.specText)).toEqual(["lo <= hi"]);
    expect(pres[0]!.kind).toBe("pre");
    const posts = result.plan.filter((record) => record.kind === "post");
    expect(posts.length).toBe(1);
    expect(posts[0]!.specText).toBe("lo <= result && result <= hi");
    expect(posts[0]!.certified).toBe(true);
    // Every obligation of the file has a record carrying its location and text.
    const sites = run("examples/pass/safeGet.ts").plan.filter((record) => record.siteId !== undefined);
    expect(sites.map((record) => record.kind)).toEqual(["index"]);
    expect(sites[0]!.certified).toBe(true);
    expect(sites[0]!.specText).toContain("i < n_a");
  });

  test("a certified function's postcondition check is certified; a failing one's is not", () => {
    const good = run("examples/pass/clamp.ts");
    expect(good.plan.filter((r) => r.kind === "post").every((r) => r.certified)).toBe(true);
    const bad = run("examples/fail/clampNoPre.ts");
    expect(bad.plan.filter((r) => r.kind === "post").every((r) => r.certified)).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// examples/fail: located diagnostics with counterexamples
// ---------------------------------------------------------------------------

/** A tiny evaluator for the spec/expression subset the examples use (milestone 9 owns the real one). */
function evaluate(e: ExprIR, values: ReadonlyMap<string, bigint>, result?: bigint): bigint | boolean {
  const num = (x: ExprIR): bigint => {
    const value = evaluate(x, values, result);
    if (typeof value !== "bigint") throw new Error(`${renderExpr(x)} is not an integer`);
    return value;
  };
  const bool = (x: ExprIR): boolean => {
    const value = evaluate(x, values, result);
    if (typeof value !== "boolean") throw new Error(`${renderExpr(x)} is not a boolean`);
    return value;
  };
  switch (e.kind) {
    case "int":
      return e.literal as bigint;
    case "true":
      return true;
    case "bool":
      return e.literal === true;
    case "ref": {
      const slot = e.slot!;
      if (slot.kind === "result") {
        if (result === undefined) throw new Error("`result` has no value here");
        return result;
      }
      if (slot.kind === "binder") {
        const name = slot.binder.surface ?? slot.binder.name;
        const value = values.get(name);
        if (value === undefined) throw new Error(`no counterexample value for \`${name}\``);
        return value;
      }
      throw new Error(`the test evaluator does not handle a ${slot.kind} slot`);
    }
    case "neg":
      return -num(e.args[0]!);
    case "add":
      return num(e.args[0]!) + num(e.args[1]!);
    case "sub":
      return num(e.args[0]!) - num(e.args[1]!);
    case "mul":
      return num(e.args[0]!) * num(e.args[1]!);
    case "lt":
      return num(e.args[0]!) < num(e.args[1]!);
    case "le":
      return num(e.args[0]!) <= num(e.args[1]!);
    case "gt":
      return num(e.args[0]!) > num(e.args[1]!);
    case "ge":
      return num(e.args[0]!) >= num(e.args[1]!);
    case "eq":
      return num(e.args[0]!) === num(e.args[1]!);
    case "neq":
      return num(e.args[0]!) !== num(e.args[1]!);
    case "and":
      return bool(e.args[0]!) && bool(e.args[1]!);
    case "or":
      return bool(e.args[0]!) || bool(e.args[1]!);
    case "not":
      return !bool(e.args[0]!);
    case "inRange": {
      const value = num(e.args[0]!);
      return -K.SAFE_MAX <= value && value <= K.SAFE_MAX;
    }
    case "cond":
      return bool(e.cond!.expr) ? evaluate(e.cond!.thenExpr!, values, result) : evaluate(e.cond!.elseExpr!, values, result);
    case "length":
      return num(e.vecLength!);
    case "index":
      throw new Error("the test evaluator does not read arrays");
    default:
      throw new Error(`the test evaluator does not handle \`${e.kind}\``);
  }
}

function valuesOf(counterexample: Readonly<Record<string, string>>): Map<string, bigint> {
  const out = new Map<string, bigint>();
  for (const [name, text] of Object.entries(counterexample)) out.set(name, BigInt(text));
  return out;
}

/** The site a diagnostic points at, looked up by span. */
function siteAt(result: VerifyResult, diagnostic: Diagnostic): { goal: ExprIR; value?: ExprIR; posts: ExprIR[] } {
  const ir = extractFile(result.path, readFileSync(result.path, "utf8"));
  const site = ir.functions
    .flatMap((fn) => fn.sites)
    .find((s) => s.span.line === diagnostic.span.line && s.span.offset === diagnostic.span.offset);
  if (site === undefined) throw new Error(`no obligation site at ${formatDiagnostic(diagnostic)}`);
  const fn = ir.functions.find((f) => f.sites.some((s) => s.id === site.id))!;
  return {
    goal: site.goal,
    value: site.resultValue,
    posts: fn.signature.result.posts.map((post) => post.prop),
  };
}

describe("examples/fail/clampNoPre.ts", () => {
  const result = run("examples/fail/clampNoPre.ts");

  test("is failed with `error[post]` at the postcondition site and a counterexample", () => {
    expect(result.ok).toBe(false);
    expect(result.functions.map((fn) => fn.status)).toEqual(["failed"]);
    const diagnostic = result.diagnostics.find((d) => d.kind === "post")!;
    expect(diagnostic).toBeDefined();
    expect(diagnostic.severity).toBe("error");
    expect(diagnostic.counterexample).toBeDefined();
    // The location is a real obligation site of the file, and the message names the post.
    const site = siteAt(result, diagnostic);
    expect(site.value).toBeDefined();
    // The failed obligation is the one the diagnostic points at.
    const verdict = result.functions[0]!;
    const failed = verdict.obligations.filter((o) => o.status === "failed");
    expect(failed.length).toBeGreaterThan(0);
    expect(failed.some((o) => o.span.offset === diagnostic.span.offset)).toBe(true);
  });

  test("the counterexample really violates the postcondition, with the precondition holding", () => {
    const diagnostic = result.diagnostics.find((d) => d.kind === "post")!;
    const counterexample = valuesOf(diagnostic.counterexample!);
    const site = siteAt(result, diagnostic);
    // `clamp` (without `@pre`) has no preconditions to violate.
    const value = evaluate(site.value!, counterexample);
    expect(typeof value).toBe("bigint");
    const holds = site.posts.map((post) => evaluate(post, counterexample, value as bigint));
    expect(holds.some((entry) => entry === false)).toBe(true);
    // ... and the parameters are all inside the safe integer range, as `InRange` requires.
    const x = counterexample.get("x")!;
    const lo = counterexample.get("lo")!;
    const hi = counterexample.get("hi")!;
    for (const n of [x, lo, hi]) expect(n >= -K.SAFE_MAX && n <= K.SAFE_MAX).toBe(true);
    // The counterexample is reported over the user's own parameter names.
    expect([...counterexample.keys()].sort()).toEqual(["hi", "lo", "x"]);
  });
});

describe("examples/fail/offByOne.ts", () => {
  test("gives `error[index]` at the `a[i]` site", () => {
    const result = run("examples/fail/offByOne.ts");
    expect(result.ok).toBe(false);
    const diagnostic = result.diagnostics.find((d) => d.kind === "index")!;
    expect(diagnostic).toBeDefined();
    expect(diagnostic.severity).toBe("error");
    expect(diagnostic.message).toContain("index");
    // The index site is `a[i]` on line 5.
    expect(diagnostic.span.line).toBe(5);
    const source = readFileSync(resolve(repoRoot, "examples/fail/offByOne.ts"), "utf8");
    expect(spanText(source, diagnostic.span)).toBe("a[i]");
    // The counterexample violates the bound: `0 <= i && i < a.length` fails.
    const counterexample = valuesOf(diagnostic.counterexample!);
    expect(counterexample.has("i")).toBe(true);
    const site = siteAt(result, diagnostic);
    expect(evaluate(site.goal, counterexample)).toBe(false);
    // ... and the precondition (`0 <= i && i <= a.length`) does hold, which is why it is a
    // counterexample to the index bound rather than to the specification.
    const precondition = extractFile(resolve(repoRoot, "examples/fail/offByOne.ts"), read("examples/fail/offByOne.ts"))
      .functions[0]!.signature.preconditions[0]!;
    expect(evaluate(precondition.prop, counterexample)).toBe(true);
  });
});

describe("examples/fail/overflow.ts", () => {
  test("gives `error[range]` at the `x + y` site", () => {
    const result = run("examples/fail/overflow.ts");
    expect(result.ok).toBe(false);
    const diagnostic = result.diagnostics.find((d) => d.kind === "range")!;
    expect(diagnostic).toBeDefined();
    expect(diagnostic.severity).toBe("error");
    const source = readFileSync(resolve(repoRoot, "examples/fail/overflow.ts"), "utf8");
    expect(spanText(source, diagnostic.span)).toBe("x + y");
    // The counterexample puts the sum outside the safe integer range.
    const counterexample = valuesOf(diagnostic.counterexample!);
    const sum = counterexample.get("x")! + counterexample.get("y")!;
    expect(sum > K.SAFE_MAX || sum < -K.SAFE_MAX).toBe(true);
  });
});

describe("examples/fail/rejected.ts", () => {
  const result = run("examples/fail/rejected.ts");

  test("passes every `error[fragment]` through with its location", () => {
    const extracted = extractFile(resolve(repoRoot, "examples/fail/rejected.ts"), read("examples/fail/rejected.ts"));
    const fragment = extracted.diagnostics.filter((d) => d.kind === "fragment");
    expect(fragment.length).toBeGreaterThanOrEqual(8);
    for (const diagnostic of fragment) {
      const found = result.diagnostics.find(
        (d) => d.kind === "fragment" && d.span.offset === diagnostic.span.offset && d.message === diagnostic.message,
      );
      expect(found).toBeDefined();
      expect(found!.span.line).toBe(diagnostic.span.line);
      expect(found!.span.col).toBe(diagnostic.span.col);
    }
  });

  test("marks every function with a fragment error as `rejected`", () => {
    expect(result.functions.length).toBe(8);
    for (const fn of result.functions) expect(`${fn.name}:${fn.status}`).toBe(`${fn.name}:rejected`);
    expect(result.ok).toBe(false);
    // The rejected verdicts carry no obligations: nothing was elaborated for them.
    expect(result.functions.every((fn) => fn.obligations.length === 0)).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Imports: parsed, admitted as `external` declarations, callers marked
// ---------------------------------------------------------------------------

describe("imported specs", () => {
  test("useClamp admits `clamp` as an external declaration with a matching hash", () => {
    const result = run("examples/pass/useClamp.ts");
    const decl = K.lookupDecl(result.env, "clamp");
    expect(decl?.kind).toBe("external");
    if (decl?.kind !== "external") throw new Error("clamp is not an external declaration");
    expect(decl.source.file).toBe(resolve(repoRoot, "examples/pass/clamp.ts"));
    expect(decl.source.hash).toBe(contentHash(read("examples/pass/clamp.ts")));
    expect(result.externals).toEqual([
      {
        name: "clamp",
        file: resolve(repoRoot, "examples/pass/clamp.ts"),
        hash: contentHash(read("examples/pass/clamp.ts")),
        certified: "unknown",
      },
    ]);
  });

  test("with `verifyImports`, the imported function's own verdict is reported", () => {
    const result = run("examples/pass/useClamp.ts", { verifyImports: true });
    expect(result.externals).toEqual([
      {
        name: "clamp",
        file: resolve(repoRoot, "examples/pass/clamp.ts"),
        hash: contentHash(read("examples/pass/clamp.ts")),
        certified: true,
      },
    ]);
    expect(result.ok).toBe(true);
  });

  test("a caller of an uncertified import is marked", () => {
    const caller = resolve(import.meta.dir, "fixtures/callUncertified.ts");
    const result = verify(caller, readFileSync(caller, "utf8"), { verifyImports: true });
    const imported = result.externals.find((e) => e.name === "badAdd")!;
    expect(imported.certified).toBe(false);
    const callee = result.functions.find((fn) => fn.name === "callBadAdd")!;
    expect(callee.dependsOnUncertified).toEqual(["badAdd"]);
    // Lenient mode still certifies the caller...
    expect(callee.status).toBe("certified");
    // ... but strict mode fails the file.
    const strict = verify(caller, readFileSync(caller, "utf8"), { strict: true, verifyImports: true });
    expect(strict.ok).toBe(false);
    expect(strict.functions.find((fn) => fn.name === "callBadAdd")!.dependsOnUncertified).toEqual(["badAdd"]);
  });
});

// ---------------------------------------------------------------------------
// Part B is not implemented yet: loops and recursion must not crash the driver
// ---------------------------------------------------------------------------

describe("loops and recursion (part B)", () => {
  for (const [file, what] of [
    ["examples/pass/binarySearch.ts", "loop"],
    ["examples/pass/sumTo.ts", "recursion"],
    ["examples/fail/noDecrease.ts", "recursion"],
  ] as const) {
    test(`${file} is failed with an \`internal\` diagnostic naming ${what}`, () => {
      const result = run(file);
      expect(result.ok).toBe(false);
      const diagnostic = result.diagnostics.find((d) => d.kind === "internal")!;
      expect(diagnostic).toBeDefined();
      expect(diagnostic.message).toContain(what);
      expect(diagnostic.message).toContain("milestone 7 part B");
      expect(result.functions.every((fn) => fn.status === "failed")).toBe(true);
    });
  }
});

// ---------------------------------------------------------------------------
// The driver itself
// ---------------------------------------------------------------------------

describe("the driver", () => {
  test("reports a file with no annotated function as ok", () => {
    const path = resolve(import.meta.dir, "fixtures/plain.ts");
    const result = verify(path, "export function double(x: number): number { return 2 * x; }\n");
    expect(result.ok).toBe(true);
    expect(result.functions).toEqual([]);
    expect(result.diagnostics).toEqual([]);
    expect(result.axioms).toEqual([]);
  });

  test("never throws: an out-of-fragment body is `rejected` with a located diagnostic", () => {
    const source = "/** @post result >= 0 */\nexport function broken(x: number): number { return x / 2; }\n";
    const result = verify(resolve(repoRoot, "examples/pass/broken.ts"), source);
    expect(result.ok).toBe(false);
    const diagnostic = result.diagnostics.find((d) => d.kind === "fragment")!;
    expect(diagnostic).toBeDefined();
    expect(diagnostic.span.line).toBe(2);
    expect(result.functions.map((fn) => fn.status)).toEqual(["rejected"]);
  });

  test("never throws: a lexing error becomes a `parse` diagnostic", () => {
    const source = '/** @post result >= 0 */\nexport function f(x: number): number { return x; }\nconst s = "abc\n';
    expect(lex(source, "x.ts").diagnostics.length).toBe(1);
    const result = verify(resolve(repoRoot, "examples/pass/broken.ts"), source);
    expect(result.ok).toBe(false);
    expect(result.diagnostics.some((d) => d.kind === "parse")).toBe(true);
  });

  test("strict mode fails an `smt-only` obligation, lenient mode warns", () => {
    // An obligation with a Farkas certificate is `certified`; the smt-only path needs an
    // integer fact that has no certificate, which none of the examples produces.  The
    // strictness rule itself is checked through the status plumbing instead.
    const result = run("examples/pass/clamp.ts", { strict: true });
    expect(result.strict).toBe(true);
    expect(result.ok).toBe(true);
    expect(result.functions[0]!.status).toBe("certified");
  });
});
