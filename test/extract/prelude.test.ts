/**
 * Milestone 5: the prelude — the JS built-ins the verifier trusts, mapped to kernel
 * *definitions* (section 6.3), and everything else under `Math.*` rejected with a location.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import {
  ctxOfSite,
  exprTerm,
  extractFile,
  type FunctionIR,
} from "../../src/extract/fragment";
import { lookupMathBuiltin, preludeNames } from "../../src/extract/prelude";

const env = K.emptyEnv();

/** The kernel term of the expression a function returns, from its `post` site. */
function returnedTerm(fn: FunctionIR, index = 0): K.Term {
  const sites = fn.sites.filter((s) => s.kind === "post");
  const site = sites[index]!;
  expect(site.resultValue).toBeDefined();
  return exprTerm(ctxOfSite(site), site.resultValue!);
}

function extractFunction(body: string, params = "x: number, y: number", tags = "@post result >= 0"): FunctionIR {
  const source = `/**\n * ${tags}\n */\nexport function f(${params}): number {\n${body}\n}\n`;
  const ir = extractFile("synthetic.ts", source);
  expect(ir.diagnostics).toEqual([]);
  return ir.functions[0]!;
}

describe("the prelude table", () => {
  test("has exactly the five documented entries", () => {
    expect(preludeNames()).toEqual(["Math.max", "Math.min", "Math.abs", "Math.floor", "Math.trunc"]);
  });

  test("`Math.max(a, b)` is `ifLe a b (_ => b) (_ => a)`", () => {
    const builtin = lookupMathBuiltin("Math.max")!;
    const built = builtin.build([K.intLit(3n), K.intLit(7n)]);
    const a = K.intLit(3n);
    const b = K.intLit(7n);
    const expected = K.IfLe(
      0,
      K.Int,
      a,
      b,
      K.lam("_", K.Le(a, b), b),
      K.lam("_", K.Lt(b, a), a),
    );
    expect(K.formatTerm(built)).toBe(K.formatTerm(expected));
    expect(K.isConvertible(env, built, K.intLit(7n))).toBe(true);
  });

  test("`Math.min` picks the other branch and `Math.abs` negates below zero", () => {
    const min = lookupMathBuiltin("Math.min")!;
    expect(K.isConvertible(env, min.build([K.intLit(3n), K.intLit(7n)]), K.intLit(3n))).toBe(true);
    const abs = lookupMathBuiltin("Math.abs")!;
    expect(K.isConvertible(env, abs.build([K.intLit(-4n)]), K.intLit(4n))).toBe(true);
    expect(K.isConvertible(env, abs.build([K.intLit(4n)]), K.intLit(4n))).toBe(true);
  });

  test("`Math.floor`/`Math.trunc` map to divFloor/divTrunc", () => {
    const floor = lookupMathBuiltin("Math.floor")!;
    const trunc = lookupMathBuiltin("Math.trunc")!;
    expect(K.formatTerm(floor.build([K.intLit(7n), K.intLit(2n)]))).toBe(
      K.formatTerm(K.DivFloor(K.intLit(7n), K.intLit(2n))),
    );
    expect(K.formatTerm(trunc.build([K.intLit(-7n), K.intLit(2n)]))).toBe(
      K.formatTerm(K.DivTrunc(K.intLit(-7n), K.intLit(2n))),
    );
    expect(K.isConvertible(env, floor.build([K.intLit(7n), K.intLit(2n)]), K.intLit(3n))).toBe(true);
    expect(K.isConvertible(env, trunc.build([K.intLit(-7n), K.intLit(2n)]), K.intLit(-3n))).toBe(true);
  });

  test("every other `Math.*` member is outside the table", () => {
    for (const name of ["Math.sqrt", "Math.pow", "Math.sin", "Math.random", "Math.PI"]) {
      expect(lookupMathBuiltin(name)).toBeUndefined();
    }
  });
});

describe("the prelude in a verified body", () => {
  test("`Math.abs(x)` becomes the kernel definition of the absolute value", () => {
    const fn = extractFunction("  return Math.abs(x);");
    const term = returnedTerm(fn);
    // The site context is `x, r_x, y, r_y`: `x` is de Bruijn index 3 and `y` index 1.
    const x = K.varTerm(3);
    const expected = K.IfLe(
      0,
      K.Int,
      K.intLit(0n),
      x,
      K.lam("_", K.Le(K.intLit(0n), x), K.varTerm(4)),
      K.lam("_", K.Lt(x, K.intLit(0n)), K.Neg(K.varTerm(4))),
    );
    expect(K.formatTerm(term)).toBe(K.formatTerm(expected));
    // The site's own goal records the `range` obligation for the result.
    expect(fn.sites.some((s) => s.kind === "range" && s.text.includes("Math.abs"))).toBe(true);
  });

  test("`Math.max`/`Math.min` accept two arguments and reject the wrong arity", () => {
    expect(extractFunction("  return Math.max(x, y);").sites.length).toBeGreaterThan(0);
    const ir = extractFile(
      "synthetic.ts",
      "/**\n * @post result >= 0\n */\nexport function f(x: number, y: number): number {\n  return Math.max(x);\n}\n",
    );
    expect(ir.diagnostics.some((d) => d.message.includes("takes exactly 2 argument(s)"))).toBe(true);
  });

  test("`Math.floor(e / k)` records the division lemma and reduces on literals", () => {
    const fn = extractFunction("  return Math.floor((x + y) / 2);");
    const term = returnedTerm(fn);
    expect(K.formatTerm(term)).toBe(K.formatTerm(K.DivFloor(K.Add(K.varTerm(3), K.varTerm(1)), K.intLit(2n))));
    expect(fn.sites.some((s) => s.kind === "range")).toBe(true);
    expect(K.isConvertible(env, K.DivFloor(K.intLit(7n), K.intLit(2n)), K.intLit(3n))).toBe(true);
  });

  test("`Math.trunc(e / k)` maps to divTrunc and needs the sign split", () => {
    const fn = extractFunction("  return Math.trunc((x + y) / 3);");
    expect(K.formatTerm(returnedTerm(fn))).toBe(
      K.formatTerm(K.DivTrunc(K.Add(K.varTerm(3), K.varTerm(1)), K.intLit(3n))),
    );
  });
});

describe("prelude rejections", () => {
  function errorFor(body: string, params = "x: number, y: number") {
    const source = `/**\n * @post result >= 0\n */\nexport function f(${params}): number {\n${body}\n}\n`;
    const ir = extractFile("synthetic.ts", source);
    return ir.diagnostics.filter((d) => d.kind === "fragment");
  }

  test("division by a non-literal is rejected at the divisor", () => {
    const errors = errorFor("  return Math.floor(x / y);");
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("the divisor must be a positive integer literal");
    expect(errors[0]!.span.line).toBe(5);
  });

  test("a non-positive literal divisor is rejected", () => {
    expect(errorFor("  return Math.floor(x / 0);")[0]!.message).toContain("positive integer literal");
    expect(errorFor("  return Math.floor(x / -2);")[0]!.message).toContain("positive integer literal");
  });

  test("`/` outside the floor/trunc forms is rejected", () => {
    expect(errorFor("  return x / 2;")[0]!.message).toContain("`/` is only allowed");
  });

  test("`Math.sqrt` is not in the prelude", () => {
    const errors = errorFor("  return Math.sqrt(x);");
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("`Math.sqrt` is not in the verified prelude");
    expect(errors[0]!.span.line).toBe(5);
  });

  test("`%` is rejected", () => {
    expect(errorFor("  return x % 2;")[0]!.message).toContain("`%` is not allowed");
  });

  test("a call to an unverified function is rejected", () => {
    const source =
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return g(x);\n}\n" +
      "export function g(x: number): number {\n  return x;\n}\n";
    const errors = extractFile("synthetic.ts", source).diagnostics.filter((d) => d.kind === "fragment");
    expect(errors[0]!.message).toContain("is not a verified function");
  });
});
