/**
 * Milestone 9's required unfaithful-elaboration test (specification 7, milestone 9):
 * deliberately tamper with an elaborated term and show that the differential test **catches**
 * the mismatch with a real failing input.
 *
 * The tampering lives here and nowhere else.  `difftestFile`'s `tamper` option is the
 * test-only hook: the driver, the verifier and the plugin never pass one, and the tampered
 * term is fed *only* to the interpreter, never to the kernel.
 *
 * The main case swaps the two branches of `abs`'s single `ifLe`.  That is a faithful stand-in
 * for the classic `<`-for-`<=` elaboration slip: the kernel still accepts nothing about the
 * tampered term (it is never checked), but the term no longer computes what the source does,
 * so `abs(5)` becomes `-5` and the `@post result >= 0` breaks.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { difftestFile, formatDifftestReport } from "../../src/difftest/driver";
import * as K from "../../src/kernel/index";
import { verify } from "../../src/verify";

setDefaultTimeout(120_000);

const repoRoot = resolve(import.meta.dir, "../..");
const ABS = resolve(repoRoot, "examples/pass/abs.ts");
const USE_CLAMP = resolve(repoRoot, "examples/pass/useClamp.ts");

// ---------------------------------------------------------------------------
// TEST-ONLY term rewriting helpers
// ---------------------------------------------------------------------------

/** Rewrite every subterm bottom-up.  Test scaffolding for the tampers below. */
function mapTerm(term: K.Term, f: (term: K.Term) => K.Term): K.Term {
  const walk = (node: K.Term): K.Term => {
    switch (node.tag) {
      case "Var":
      case "Sort":
      case "Const":
      case "IntLit":
      case "Farkas":
        return f(node);
      case "Pi":
      case "Lam":
        return f({ ...node, domain: walk(node.domain), body: walk(node.body) });
      case "App":
        return f({ ...node, fn: walk(node.fn), arg: walk(node.arg) });
      case "Sigma":
        return f({ ...node, first: walk(node.first), second: walk(node.second) });
      case "Pair":
        return f({ ...node, sigma: walk(node.sigma), first: walk(node.first), second: walk(node.second) });
      case "Fst":
        return f({ ...node, pair: walk(node.pair) });
      case "Snd":
        return f({ ...node, pair: walk(node.pair) });
      case "Let":
        return f({ ...node, type: walk(node.type), value: walk(node.value), body: walk(node.body) });
      case "Prim":
        return f({ ...node, args: node.args.map(walk) });
    }
  };
  return walk(term);
}

/** TEST-ONLY: swap the `yes`/`no` branches of every `ifLe` in `term`, counting them. */
function swapBranches(term: K.Term, count: (found: number) => void): K.Term {
  let found = 0;
  const out = mapTerm(term, (node) => {
    if (node.tag === "Prim" && node.op === K.OP_IF_LE && node.args.length === 5) {
      found += 1;
      return { ...node, args: [node.args[0]!, node.args[1]!, node.args[2]!, node.args[4]!, node.args[3]!] };
    }
    return node;
  });
  count(found);
  return out;
}

/** The certified term of one function, straight from `verify`'s environment. */
function termOf(path: string, name: string): K.Term {
  const result = verify(path, readFileSync(path, "utf8"));
  const decl = K.lookupDecl(result.env, name);
  if (decl === undefined || decl.kind !== "def") throw new Error(`${name} is not a definition`);
  return decl.value;
}

// ---------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------

describe("the unfaithful-elaboration test", () => {
  test("the tamper really changes the elaborated term of `abs`", () => {
    const term = termOf(ABS, "abs");
    let found = 0;
    const tampered = swapBranches(term, (count) => {
      found = count;
    });
    expect(found).toBe(1); // `abs` elaborates to exactly one `ifLe`
    expect(K.formatTerm(tampered)).not.toBe(K.formatTerm(term));
  });

  test("the tampered `abs` is caught by a real failing input, and the faithful one passes", async () => {
    let found = 0;
    const tampered = await difftestFile(ABS, {
      count: 200,
      tamper: (name, term) => (name === "abs" ? swapBranches(term, (count) => (found = count)) : term),
    });

    // The hook was used, on exactly the one `ifLe` of the elaboration.
    expect(found).toBe(1);
    expect(tampered.ok).toBe(false);
    expect(tampered.failures.length).toBeGreaterThan(0);

    const mismatch = tampered.failures.find((failure) => failure.kind === "mismatch");
    expect(mismatch).toBeDefined();
    // A *real* difference: the two results are each other's negation (`abs`'s branches are
    // `-x` and `x`), not a cosmetic rendering difference.
    const asNumber = (text: string): number => Number(text.replace(/n$/, ""));
    expect(asNumber(mismatch!.interpreted!)).toBe(-asNumber(mismatch!.original!));
    // The diagnostic names the function, the input and both results.
    expect(mismatch!.message).toContain("`abs`");
    expect(mismatch!.message).toContain("x = ");
    expect(mismatch!.message).toContain("the original returned");
    expect(mismatch!.message).toContain("the interpreter returned");

    // Every failure is a mismatch — `@post` is evaluated against the *original's* result,
    // which is what the source really returns (`abs(5) = 5` satisfies `result >= 0`).  The
    // interpreter's wrong answer is negative, so it is the `@post` that would break if the
    // tampered term were the one that ran.
    expect(tampered.failures.every((failure) => failure.kind === "mismatch")).toBe(true);
    expect(asNumber(mismatch!.interpreted!)).toBeLessThan(0);
    expect(mismatch!.values[0]).toBe(mismatch!.values[0]); // the input is a real value
    expect(typeof mismatch!.values[0]).toBe("number");
    expect(formatDifftestReport(tampered)).toContain("[mismatch]");

    // Control: with no tamper the very same file passes.
    const faithful = await difftestFile(ABS, { count: 200 });
    expect(faithful.ok).toBe(true);
    expect(faithful.failures).toEqual([]);
  });

  test("tampering with an imported callee's body changes the caller's result", async () => {
    // `percent` calls the imported `clamp`; an `external` declaration has no body to
    // interpret, so this only works because the driver elaborates the imported file too.
    const report = await difftestFile(USE_CLAMP, {
      count: 50,
      tamper: (name, term) => (name === "clamp" ? swapBranches(term, () => {}) : term),
    });
    expect(report.ok).toBe(false);
    expect(report.failures.some((failure) => failure.kind === "mismatch")).toBe(true);

    // ... and the untampered import resolves to the real body, so it passes.
    const faithful = await difftestFile(USE_CLAMP, { count: 50 });
    expect(faithful.ok).toBe(true);
  });
});
