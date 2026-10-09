/**
 * Cross-check tests (section 9.2): agreement for every annotated function in
 * `examples/`, detection of a deliberately broken parse, and one case per
 * statement kind proving that Bun normalises our printout identically.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { Glob } from "bun";
import type * as A from "../../src/syntax/ast";
import { crosscheckFunction, normalizeWithBun, sameParse } from "../../src/syntax/crosscheck";
import { lex } from "../../src/syntax/lexer";
import { parseFile } from "../../src/syntax/parser";
import { printFunction } from "../../src/syntax/print";

const repoRoot = new URL("../..", import.meta.url).pathname;
const exampleFiles = [
  ...new Glob("examples/**/*.ts").scanSync({ cwd: repoRoot, absolute: true }),
].sort();

function sourceOf(file: string): string {
  return readFileSync(file, "utf8");
}

/** Parse a function wrapped in an annotation, asserting it parsed cleanly. */
function parseAnnotated(body: string): { fn: A.FnDecl; source: string } {
  const source = `/**\n * @post result === 0\n */\nexport function f(a: number, b: number, c: number): number {\n${body}\n}\n`;
  const parsed = parseFile("case.ts", source);
  expect(parsed.diagnostics).toEqual([]);
  expect(parsed.functions.length).toBe(1);
  return { fn: parsed.functions[0]!, source };
}

describe("examples", () => {
  test("every example file lexes without throwing and without errors", () => {
    expect(exampleFiles.length).toBeGreaterThanOrEqual(14);
    for (const file of exampleFiles) {
      const source = sourceOf(file);
      let result: ReturnType<typeof lex> | undefined;
      expect(() => {
        result = lex(source, file);
      }).not.toThrow();
      expect(result!.diagnostics).toEqual([]);
      expect(result!.tokens.some((t) => t.kind === "eof")).toBe(true);
    }
  });

  test("every annotated function in every example parses with no parse diagnostics", () => {
    for (const file of exampleFiles) {
      const parsed = parseFile(file, sourceOf(file));
      expect(parsed.diagnostics).toEqual([]);
    }
  });

  test("every annotated function in `examples/pass` passes the cross-check", () => {
    const checked: string[] = [];
    for (const file of exampleFiles.filter((f) => f.includes("/pass/"))) {
      const source = sourceOf(file);
      const parsed = parseFile(file, source);
      expect(parsed.functions.length).toBeGreaterThan(0);
      for (const fn of parsed.functions) {
        const diagnostic = crosscheckFunction(fn, source);
        expect(diagnostic).toBeNull();
        checked.push(fn.name);
      }
    }
    expect(checked).toEqual([
      "abs",
      "binarySearch",
      "clamp",
      "concat",
      "safeGet",
      "perimeter",
      "sumTo",
      "take",
      "percent",
    ]);
  });

  test("the deliberately rejected examples parse too, so milestone 5 can name the construct", () => {
    for (const file of exampleFiles.filter((f) => f.includes("/fail/"))) {
      const source = sourceOf(file);
      const parsed = parseFile(file, source);
      expect(parsed.diagnostics).toEqual([]);
      for (const fn of parsed.functions) {
        expect(crosscheckFunction(fn, source)).toBeNull();
      }
    }
  });

  test("`examples/fail/rejected.ts` has one annotated function per rejected construct", () => {
    const file = `${repoRoot}examples/fail/rejected.ts`;
    const source = sourceOf(file);
    const parsed = parseFile(file, source);
    expect(parsed.functions.map((f) => f.name)).toEqual([
      "anyParameter",
      "asCast",
      "parameterMutation",
      "plainDivision",
      "throwStatement",
      "floatLiteral",
      "thisExpression",
      "moduloOperator",
    ]);
  });

  test("the parser never throws on this repository's own TypeScript", () => {
    const files = [
      ...new Glob("{src,test,scripts}/**/*.ts").scanSync({ cwd: repoRoot, absolute: true }),
    ].sort();
    expect(files.length).toBeGreaterThan(20);
    for (const file of files) {
      const source = sourceOf(file);
      expect(() => parseFile(file, source)).not.toThrow();
    }
  });

  test("type aliases are not cross-checkable: Bun normalises them to nothing", () => {
    expect(normalizeWithBun("type Shape = { readonly kind: \"square\" };")).toBe("");
  });
});

describe("statement kinds normalise identically", () => {
  const CASES: Array<[string, string]> = [
    ["block", `  { const inner = a; }
  return inner;`],
    ["const declaration", `  const x: number = a + 1;
  return x;`],
    ["let declaration", `  let x = a;
  return x;`],
    ["assignment statement", `  let x = a;
  x = b;
  return x;`],
    ["compound assignments", `  let x = a;
  x += b;
  x -= b;
  x *= b;
  return x;`],
    ["increment and decrement statements", `  let x = a;
  x++;
  x--;
  ++x;
  --x;
  return x;`],
    ["if without braces", `  if (a < b) return a;
  return b;`],
    ["if with braces", `  if (a < b) { return a; }
  return b;`],
    ["if/else", `  if (a < b) { return a; } else { return b; }`],
    ["if/else without braces", `  if (a < b) return a; else return b;`],
    ["else-if chain", `  if (a < b) { return a; } else if (a > b) { return b; } else { return c; }`],
    ["return without a value", `  if (a < b) { return; }
  return a;`],
    ["switch with default", `  switch (a) {
    case 0:
      return 1;
    default:
      return 2;
  }`],
    ["switch with grouped and unreachable cases", `  switch (a) {
    case 0:
    case 1:
      return 1;
    case 2:
      return 2;
  }`],
    ["switch with a braced case body", `  switch (a) {
    case 0: {
      return 1;
    }
    default: {
      return 2;
    }
  }`],
    ["switch with break", `  let r = 0;
  switch (a) {
    case 0:
      r = 1;
      break;
    default:
      r = 2;
      break;
  }
  return r;`],
    ["while with loop JSDoc", `  let i = 0;
  /**
   * @invariant 0 <= i && i <= b
   * @decreases b - i
   */
  while (i < b) {
    i += 1;
  }
  return i;`],
    ["while without braces", `  let i = 0;
  while (i < b) i += 1;
  return i;`],
    ["for with a let initialiser", `  let total = 0;
  for (let i = 0; i < b; i++) {
    total += i;
  }
  return total;`],
    ["for with loop JSDoc and a compound update", `  let total = 0;
  /**
   * @invariant 0 <= total
   * @decreases b - total
   */
  for (let i = 0; i < b; i += 2) {
    total += i;
  }
  return total;`],
    ["for with an empty header", `  let i = 0;
  for (;;) {
    if (i < b) break;
  }
  return i;`],
    ["for with a comma update", `  let i = 0;
  let j = 0;
  for (i = 0, j = 1; i < b; i++, j++) {
    j = j;
  }
  return i;`],
    ["empty statement", `  ;
  return a;`],
    ["throw statement", `  if (a < b) { throw new Error("no"); }
  return a;`],
    ["continue inside a loop", `  let i = 0;
  while (i < b) {
    i += 1;
    if (i < a) continue;
    i += 1;
  }
  return i;`],
    ["break inside a loop", `  let i = 0;
  while (i < b) {
    if (i < a) break;
    i += 1;
  }
  return i;`],
    ["nested function declaration", `  function helper(x: number): number { return x; }
  return helper(a);`],
    ["try/catch/finally", `  try { return a; } catch { return b; } finally { }`],
    ["do/while", `  let i = 0;
  do { i += 1; } while (i < a);
  return i;`],
    ["for-of", `  let total = 0;
  for (const x of [1, 2]) { total += x; }
  return total;`],
    ["class declaration", `  class K { m(): number { return 1; } }
  return a;`],
    ["array elision", `  const xs = [1, , 2];
  return a;`],
    ["single-line array and object literals", `  const xs = [a, b];
  const o = { kind: "x", n: a };
  return a;`],
    ["multi-line object literal", `  return {
    kind: "square",
    side: a,
  };`],
    ["multi-line array literal", `  return [
    a,
    b,
  ];`],
    ["multi-line literal nested in a single-line one", `  return { list: [
    a,
  ], n: b };`],
    ["single-line literal nested in a multi-line one", `  return {
    list: [a, b],
    n: c,
  };`],
    ["comments inside the body", `  // a line comment
  /* and a block comment */
  return a;`],
    ["expression statements with calls and member access", `  const xs = [a, b];
  xs.slice(0, a);
  return xs.length;`],
  ];

  for (const [label, body] of CASES) {
    test(label, () => {
      const { fn, source } = parseAnnotated(body);
      expect(crosscheckFunction(fn, source)).toBeNull();
    });
  }
});

describe("broken parses are detected", () => {
  test("`a - b - c` printed as `a - (b - c)` does not parse the same", () => {
    const { fn } = parseAnnotated("  return a - b - c;");
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
    const broken = fn.text.replace("a - b - c", "a - (b - c)");
    expect(broken).not.toBe(fn.text);
    expect(sameParse(fn.text, broken)).toBe(false);
  });

  test("redundant parentheses are not a difference", () => {
    const { fn } = parseAnnotated("  return a - b - c;");
    const sameTree = fn.text.replace("return a - b - c;", "return ((a - b) - c);");
    expect(sameTree).not.toBe(fn.text);
    expect(sameParse(fn.text, sameTree)).toBe(true);
    const parenthesised = fn.text.replace("return a - b - c;", "return (a) - (b) - (c);");
    expect(sameParse(fn.text, parenthesised)).toBe(true);
  });

  test("a doctored AST (right-associative subtraction) yields an `internal` diagnostic", () => {
    const { fn, source } = parseAnnotated("  return a - b - c;");
    const original = fn.body.body[0] as A.ReturnStmt;
    const outer = original.argument as A.BinaryExpr;
    const inner = outer.right as A.BinaryExpr;
    // Rebuild `a - (b - c)` out of the parts of `(a - b) - c`.
    const flipped: A.BinaryExpr = {
      ...outer,
      left: outer.left,
      right: {
        ...outer,
        left: inner.left,
        right: inner.right,
      },
    };
    const doctored: A.FnDecl = {
      ...fn,
      body: {
        ...fn.body,
        body: [{ ...original, argument: flipped }],
      },
    };
    const diagnostic = crosscheckFunction(doctored, source);
    expect(diagnostic).not.toBeNull();
    expect(diagnostic!.kind).toBe("internal");
    expect(diagnostic!.severity).toBe("error");
    expect(diagnostic!.message).toContain("cross-check failed for `f`");
    expect(diagnostic!.span.file).toBe("case.ts");
  });

  test("a printer that drops a statement is detected", () => {
    const { fn, source } = parseAnnotated("  const x = a;\n  return x;");
    const dropped: A.FnDecl = {
      ...fn,
      body: { ...fn.body, body: [fn.body.body[1]!] },
    };
    const diagnostic = crosscheckFunction(dropped, source);
    expect(diagnostic).not.toBeNull();
    expect(diagnostic!.kind).toBe("internal");
  });
});
