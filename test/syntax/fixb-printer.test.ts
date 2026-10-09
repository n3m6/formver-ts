/**
 * Printer regressions found by the cross-check audit (fix 2).
 *
 * Two printer bugs made `crosscheckFunction` reject *valid* input:
 *
 *   - `a?.b.c` printed as `((a)?.b).c`: parentheses around an optional chain are semantically
 *     significant, so Bun keeps them and the two printouts differ;
 *   - `() => ({ a: 1 })` printed as `() => { a: 1 }`, which Bun reads as a block with a label.
 *
 * Both must print in the form Bun normalises back to the original, or the cross-check that
 * `verify()` now runs (fix 1) would reject correct annotated functions as `internal`.
 */
import { describe, expect, test } from "bun:test";
import type * as A from "../../src/syntax/ast";
import { crosscheckFunction, normalizeWithBun, sameParse } from "../../src/syntax/crosscheck";
import { parseFile } from "../../src/syntax/parser";
import { printExpr, printFunction } from "../../src/syntax/print";

/** Parse one annotated function and return it with its source. */
function parseAnnotated(body: string): { fn: A.FnDecl; source: string } {
  const source = `/**\n * @post result === 0\n */\nexport function f(a: number, b: number, c: number): number {\n${body}\n}\n`;
  const parsed = parseFile("case.ts", source);
  expect(parsed.diagnostics).toEqual([]);
  expect(parsed.functions.length).toBe(1);
  return { fn: parsed.functions[0]!, source };
}

/** Parse a single expression of a function body, for `printExpr` assertions. */
function parseExpression(text: string): A.Expr {
  const { fn } = parseAnnotated(`  return ${text};`);
  return (fn.body.body[0] as A.ReturnStmt).argument!;
}

describe("optional chains are not parenthesised away", () => {
  const BODIES = [
    "  return a?.b.c;",
    "  return a?.[b].c;",
    "  return f?.(a).b;",
    "  return a?.b.c.d;",
    "  return a?.b?.c;",
    "  return a?.[b]?.(c).d;",
    "  return a?.b().c;",
    "  return a.b?.c.d;",
    "  return a?.b.c + a?.b.c;",
    "  const g = () => a?.b.c;\n  return a;",
  ];

  for (const body of BODIES) {
    test(`${JSON.stringify(body)} cross-checks against Bun`, () => {
      const { fn, source } = parseAnnotated(body);
      expect(crosscheckFunction(fn, source)).toBeNull();
    });
  }

  test("the old printout really was a different parse", () => {
    // `(a?.b).c` ends the optional chain at the first link; Bun knows the difference and
    // keeps the parentheses, which is why the old printer output was rejected.
    expect(sameParse("a?.b.c", "((a)?.b).c")).toBe(false);
    expect(sameParse("a?.b.c", "(a)?.b.c")).toBe(true);
    expect(sameParse("a?.[b].c", "(a)?.[b].c")).toBe(true);
    expect(sameParse("f?.(a).b", "(f)?.(a).b")).toBe(true);
  });

  test("the printed chain drops exactly the parentheses that change the parse", () => {
    expect(printExpr(parseExpression("a?.b.c"))).toBe("(a)?.b.c");
    expect(printExpr(parseExpression("a?.[b].c"))).toBe("(a)?.[b].c");
    expect(printExpr(parseExpression("f?.(a).b"))).toBe("(f)?.(a).b");
    // A plain member access is still fully parenthesised.
    expect(printExpr(parseExpression("a.b.c"))).toBe("((a).b).c");
    expect(printExpr(parseExpression("(a + b).c"))).toBe("((a + b)).c");
  });
});

describe("object-literal arrow bodies keep their parentheses", () => {
  const BODIES = [
    "  const g = () => ({ a: 1 });\n  return a;",
    "  const g = (x: number) => ({ a: x });\n  return a;",
    "  const g = () => ({\n    a: 1,\n    b: 2,\n  });\n  return a;",
    "  const g = () => ({});\n  return a;",
    "  const g = () => f(() => ({ a: 1 }));\n  return a;",
    "  const xs = [() => ({ a: 1 })];\n  return a;",
  ];

  for (const body of BODIES) {
    test(`${JSON.stringify(body)} cross-checks against Bun`, () => {
      const { fn, source } = parseAnnotated(body);
      expect(crosscheckFunction(fn, source)).toBeNull();
    });
  }

  test("the old printout really was a block with a label", () => {
    const wrapped = "function w() {\n  return () => ({ a: 1 });\n}";
    const block = "function w() {\n  return () => { a: 1 };\n}";
    expect(normalizeWithBun(wrapped)).not.toBe(normalizeWithBun(block));
    expect(sameParse(wrapped, block)).toBe(false);
  });

  test("the printed arrow body is parenthesised", () => {
    const arrow = parseExpression("() => ({ a: 1 })");
    expect(printExpr(arrow)).toBe("(() => ({ a: 1 }))");
    // A block body is a block, not an object literal.
    const blockArrow = parseExpression("() => { return a; }");
    expect(printExpr(blockArrow)).toContain("=> {");
  });

  test("printFunction keeps the arrow object body parenthesised", () => {
    const { fn } = parseAnnotated("  const g = () => ({ a: 1 });\n  return a;");
    expect(printFunction(fn)).toContain("=> ({ a: 1 })");
  });
});
