/**
 * Milestone 5: SSA — loops become local `fixWf` functions over a tuple of carried variables,
 * with the invariant as their precondition and `@decreases` as their measure.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import * as K from "../../src/kernel/index";
import {
  extractFile,
  goalTerm,
  renderExpr,
  type FunctionIR,
  type LoopIR,
  type StmtIR,
} from "../../src/extract/fragment";

const repoRoot = resolve(import.meta.dir, "../..");

function extract(relative: string) {
  const path = resolve(repoRoot, relative);
  return extractFile(path, readFileSync(path, "utf8"));
}

function fnOf(relative: string, name: string): FunctionIR {
  const found = extract(relative).functions.find((f) => f.name === name);
  expect(found).toBeDefined();
  return found!;
}

/** Every statement in a (possibly nested) IR tree, in order. */
function walkStatements(stmts: readonly StmtIR[]): StmtIR[] {
  const out: StmtIR[] = [];
  for (const stmt of stmts) {
    out.push(stmt);
    if (stmt.kind === "if") {
      out.push(...walkStatements(stmt.then), ...walkStatements(stmt.otherwise));
    } else if (stmt.kind === "loop") {
      out.push(...walkStatements(stmt.loop.body), ...walkStatements(stmt.loop.rest));
    } else if (stmt.kind === "switch") {
      for (const c of stmt.cases) out.push(...walkStatements(c.body));
    }
  }
  return out;
}

describe("binarySearch", () => {
  const fn = fnOf("examples/pass/binarySearch.ts", "binarySearch");

  test("the loop is one local recursive function over `lo` and `hi`", () => {
    expect(fn.loops).toHaveLength(1);
    const loop: LoopIR = fn.loops[0]!;
    expect(loop.carried.map((v) => v.name)).toEqual(["lo", "hi"]);
    expect(loop.carried.map((v) => v.path)).toEqual([[0], [1, 0]]);
    expect(loop.name).toBe(`loop${loop.id}`);
    // `A = Sigma (lo : Int). Sigma (hi : Int). Unit`
    expect(K.formatTerm(loop.stateType)).toContain("Sig (lo : Int())");
    expect(K.formatTerm(loop.stateType)).toContain("Sig (hi : Int())");
  });

  test("the invariant and the measure are those of the loop's JSDoc block", () => {
    const loop = fn.loops[0]!;
    expect(renderExpr(loop.invariant)).toBe("(((0 <= lo) && (lo <= hi)) && (hi <= a.length))");
    expect(renderExpr(loop.measure)).toBe("(hi - lo)");
    expect(loop.invariantBinder.role).toBe("invariant");
    // `B = fun _ => Invariant s -> Result`
    expect(K.formatTerm(loop.resultMotive)).toContain("fun (_ :");
  });

  test("the initial state and the init obligations are recorded", () => {
    const loop = fn.loops[0]!;
    // Before the loop, `lo` and `hi` are ordinary binders (declared by `let`).
    expect(loop.carried.map((v) => renderExpr(v.initial))).toEqual(["lo", "hi"]);
    expect(loop.initSites.map((s) => s.kind)).toEqual(["invariant-init", "measure-nonneg"]);
    expect(loop.initSites[0]!.text).toBe("(((0 <= lo) && (lo <= hi)) && (hi <= a.length))");
    expect(loop.initSites[1]!.text).toBe("(0 <= (hi - lo))");
  });

  test("early `return mid` inside the loop is a return of the loop function", () => {
    const loop = fn.loops[0]!;
    const returns = walkStatements(loop.body).filter((s) => s.kind === "return");
    expect(returns).toHaveLength(1);
    expect(returns[0]!.kind === "return" && renderExpr(returns[0]!.value)).toBe("mid");
    expect(returns[0]!.kind === "return" && returns[0]!.site.kind).toBe("post");
  });

  test("the back edge is a `continue` with the new state and the measure obligations", () => {
    const loop = fn.loops[0]!;
    const continues = walkStatements(loop.body).filter((s) => s.kind === "continue");
    // One per path through the second `if` (the continuation is duplicated, not joined).
    expect(continues).toHaveLength(2);
    for (const node of continues) {
      if (node.kind !== "continue") continue;
      expect(node.loop).toBe(loop);
      expect(node.values.map((v) => v.variable.name)).toEqual(["lo", "hi"]);
      expect(node.sites.map((s) => s.kind)).toEqual([
        "invariant-preserve",
        "measure-nonneg",
        "measure-decrease",
      ]);
    }
    // The two paths preserve the invariant with different *terms* (each branch's own new
    // binding); the rendered text is the same source proposition.
    const goals = continues.map((node) =>
      node.kind === "continue" ? K.formatTerm(goalTerm(node.sites[0]!)) : "",
    );
    expect(goals[0]).not.toBe(goals[1]);
    // The measure obligation's new state is each branch's own binding of `lo` / `hi`.
    const decreases = continues.map((node) =>
      node.kind === "continue" ? K.formatTerm(goalTerm(node.sites[2]!)) : "",
    );
    expect(decreases[0]).not.toBe(decreases[1]);
    expect(decreases[0]).toContain("sub");
  });

  test("the rest of the function is the loop's `else` branch", () => {
    const loop = fn.loops[0]!;
    const rest = walkStatements(loop.rest);
    expect(rest.filter((s) => s.kind === "return")).toHaveLength(1);
    // The loop node replaces the statements after it: the function body ends with it.
    const last = fn.body[fn.body.length - 1]!;
    expect(last.kind).toBe("loop");
  });

  test("the back-edge goals are real kernel propositions", () => {
    const loop = fn.loops[0]!;
    const continues = walkStatements(loop.body).filter((s) => s.kind === "continue");
    for (const node of continues) {
      if (node.kind !== "continue") continue;
      const decrease = node.sites.find((s) => s.kind === "measure-decrease")!;
      const term = goalTerm(decrease);
      // `Lt (m new) (m state)`: the right-hand side is `hi - lo` over the state binder.
      expect(K.formatTerm(term)).toStartWith("(Lt ");
    }
  });
});

describe("sumTo", () => {
  const fn = fnOf("examples/pass/sumTo.ts", "sumTo");

  test("a recursive function records its `@decreases` measure and is marked recursive", () => {
    expect(fn.recursive).toBe(true);
    expect(fn.measure).toBeDefined();
    expect(renderExpr(fn.measure!)).toBe("n");
    expect(fn.loops).toHaveLength(0);
  });

  test("the recursive call has the pre-call and both measure obligations", () => {
    const kinds = fn.sites.map((s) => s.kind);
    expect(kinds).toContain("measure-nonneg");
    expect(kinds).toContain("measure-decrease");
    expect(kinds).toContain("pre-call");
    const decrease = fn.sites.find((s) => s.kind === "measure-decrease")!;
    expect(decrease.text).toBe("((n - 1) < n)");
    const preCall = fn.sites.find((s) => s.kind === "pre-call")!;
    expect(preCall.text).toBe("((0 <= (n - 1)) && ((n - 1) <= 1000000))");
  });

  test("the measure is a well-formed `Int`-valued expression in the parameter context", () => {
    const term = goalTerm(fn.sites.find((s) => s.kind === "measure-decrease")!);
    expect(K.formatTerm(term)).toBe("(Lt (sub(?3, 1))) ?3");
  });
});

describe("for loops", () => {
  const source =
    "/**\n * @post result >= 0\n */\n" +
    "export function count(n: number): number {\n" +
    "  let total = 0;\n" +
    "  /**\n   * @invariant 0 <= total && total <= n\n   * @decreases n - total\n   */\n" +
    "  for (let i = 0; i < n; i++) {\n    total = total + 1;\n  }\n" +
    "  return total;\n}\n";

  test("`for (let i = …; c; i++)` is desugared the same way and carries `total` and `i`", () => {
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics).toEqual([]);
    const fn = ir.functions[0]!;
    expect(fn.loops).toHaveLength(1);
    const loop = fn.loops[0]!;
    expect(loop.carried.map((v) => v.name)).toEqual(["total", "i"]);
    expect(renderExpr(loop.carried[0]!.initial)).toBe("total");
    expect(renderExpr(loop.carried[1]!.initial)).toBe("0");
    // The `i++` update is applied before the back edge.
    const updates = loop.body.filter((s) => s.kind === "local");
    expect(updates.length).toBeGreaterThanOrEqual(2);
  });

  test("a loop without a JSDoc block is rejected at the loop", () => {
    const bad = source.replace(/  \/\*\*[\s\S]*?\*\/\n/, "");
    const ir = extractFile("synthetic.ts", bad);
    expect(ir.diagnostics.some((d) => d.message.includes("needs a JSDoc block"))).toBe(true);
  });

  test("assignment outside a loop is rejected", () => {
    const bad = source.replace("  return total;", "  total = 3;\n  return total;");
    const ir = extractFile("synthetic.ts", bad);
    expect(ir.diagnostics.some((d) => d.message.includes("only be reassigned inside a loop"))).toBe(true);
  });
});
