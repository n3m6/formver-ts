/**
 * Lexer tests (section 9.2): regex versus division, template literals with
 * nested braces, comments containing `*​/`-like text, strings containing `@pre`,
 * numeric literal flags, spans and unterminated constructs.
 */
import { describe, expect, test } from "bun:test";
import { lex } from "../../src/syntax/lexer";

function kinds(source: string): string[] {
  return lex(source, "t.ts").tokens.map((t) => t.kind);
}

function texts(source: string): string[] {
  return lex(source, "t.ts")
    .tokens.filter((t) => t.kind !== "eof")
    .map((t) => t.text);
}

describe("regex versus division", () => {
  test("`a / b / c` is two division operators", () => {
    const result = lex("const r = a / b / c;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens.filter((t) => t.kind === "regex")).toEqual([]);
    expect(result.tokens.filter((t) => t.kind === "punct" && t.text === "/").length).toBe(2);
  });

  test("`x = /re/g` is a regex literal", () => {
    const result = lex("x = /re/g;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    const regex = result.tokens.find((t) => t.kind === "regex")!;
    expect(regex.regex).toEqual({ pattern: "re", flags: "g" });
  });

  test("a regex after `return` and after `(` is a regex", () => {
    expect(kinds("return /a/g;")).toContain("regex");
    expect(kinds("f(/a/g);")).toContain("regex");
    expect(kinds("case /x/:")).toContain("regex");
    expect(kinds("typeof /x/")).toContain("regex");
  });

  test("a slash after an expression is division", () => {
    expect(kinds("f() / 2")).not.toContain("regex");
    expect(kinds("a[0] / 2")).not.toContain("regex");
    expect(kinds("x++ / 2")).not.toContain("regex");
    expect(kinds("obj.k / 2")).not.toContain("regex");
  });

  test("an escaped slash and a character class do not end a regex", () => {
    const result = lex("const re = /a\\/b[/]/g;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens[3]!.regex).toEqual({ pattern: "a\\/b[/]", flags: "g" });
  });

  test("`?.` followed by a digit is not optional chaining", () => {
    expect(texts("a?.5:b")).toEqual(["a", "?", ".5", ":", "b"]);
  });
});

describe("template literals", () => {
  test("nested braces inside `${ … }` stay in one token", () => {
    const result = lex("const s = `a${ { b: 1 }.b }c`;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    const template = result.tokens.find((t) => t.kind === "template")!;
    expect(template.template!.map((p) => p.type)).toEqual(["text", "expr", "text"]);
    expect(template.text).toBe("`a${ { b: 1 }.b }c`");
  });

  test("template literals nest", () => {
    const source = "const s = `a${`b${x}c`}d`;";
    const result = lex(source, "t.ts");
    expect(result.diagnostics).toEqual([]);
    const template = result.tokens.find((t) => t.kind === "template")!;
    expect(template.text).toBe("`a${`b${x}c`}d`");
    const expr = template.template!.find((p) => p.type === "expr");
    expect(expr).toBeDefined();
    if (expr !== undefined && expr.type === "expr") {
      expect(expr.tokens.map((t) => t.text)).toEqual(["`b${x}c`", ""]);
    }
  });

  test("escaped backticks and `${` do not close or open", () => {
    const result = lex("const s = `a\\`b\\${c}`;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens.filter((t) => t.kind === "template").length).toBe(1);
  });

  test("an unterminated template is a located error", () => {
    const result = lex("const s = `abc\nconst t = 1;", "t.ts");
    expect(result.diagnostics.length).toBe(1);
    expect(result.diagnostics[0]!.kind).toBe("parse");
    expect(result.diagnostics[0]!.message).toContain("unterminated template");
    expect(result.diagnostics[0]!.span.line).toBe(1);
    expect(result.diagnostics[0]!.span.col).toBe(11);
  });
});

describe("comments", () => {
  test("a line comment containing `*/` is just a comment", () => {
    const result = lex("// */ still a comment\nx", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(texts("// */ still a comment\nx")).toEqual(["x"]);
  });

  test("a block comment containing `*/`-like text ends at the first real `*/`", () => {
    const result = lex("/* a * / b */ x", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens.map((t) => t.text).filter((t) => t !== "")).toEqual(["x"]);
  });

  test("a JSDoc block with a lone `*` or `/` inside is kept whole", () => {
    const source = "/** @pre a * / b */ function f() {}";
    const result = lex(source, "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens[0]!.text).toBe("/** @pre a * / b */");
  });

  test("JSDoc blocks are kept as tokens, other block comments are dropped", () => {
    const result = lex("/** @pre x > 0 */ /* plain */ function f() {}", "t.ts");
    expect(result.tokens[0]!.kind).toBe("jsdoc");
    expect(result.tokens[0]!.text).toBe("/** @pre x > 0 */");
    expect(result.tokens.filter((t) => t.kind === "jsdoc").length).toBe(1);
  });

  test("`/**/` is an empty comment, not a JSDoc block", () => {
    expect(kinds("/**/ x")).toEqual(["ident", "eof"]);
  });

  test("an unterminated block comment is a located error", () => {
    const result = lex("x /* never closed", "t.ts");
    expect(result.diagnostics.length).toBe(1);
    expect(result.diagnostics[0]!.span.col).toBe(3);
    expect(result.diagnostics[0]!.message).toContain("unterminated block comment");
  });
});

describe("strings and identifiers", () => {
  test("a string containing `@pre` is not JSDoc", () => {
    const result = lex('const s = "@pre x > 0";', "t.ts");
    expect(result.tokens.filter((t) => t.kind === "jsdoc")).toEqual([]);
    expect(result.tokens[3]!.kind).toBe("string");
  });

  test("all three quote kinds and escapes", () => {
    const result = lex(`const a = 'x\\'y'; const b = "x\\"y"; const c = "\\u0041\\n";`, "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens.filter((t) => t.kind === "string").map((t) => t.text)).toEqual([
      "'x\\'y'",
      '"x\\"y"',
      '"\\u0041\\n"',
    ]);
  });

  test("an unterminated string is located, and recovery continues on the next line", () => {
    const result = lex('const s = "abc\nconst t = 1;', "t.ts");
    expect(result.diagnostics.length).toBe(1);
    expect(result.diagnostics[0]!.span).toMatchObject({ line: 1, col: 11 });
    expect(result.tokens.some((t) => t.text === "const" && t.span.line === 2)).toBe(true);
  });

  test("reserved words are keywords, contextual ones are identifiers", () => {
    const result = lex("const let type of as readonly", "t.ts");
    expect(
      result.tokens.filter((t) => t.kind !== "eof").map((t) => `${t.text}:${t.kind}`),
    ).toEqual([
      "const:keyword",
      "let:ident",
      "type:ident",
      "of:ident",
      "as:ident",
      "readonly:ident",
    ]);
  });

  test("a shebang line is skipped", () => {
    const result = lex("#!/usr/bin/env bun\nconst x = 1;", "t.ts");
    expect(result.diagnostics).toEqual([]);
    expect(result.tokens[0]!.span.line).toBe(2);
  });
});

describe("numeric literals", () => {
  test("integers, floats, hex, bigint and separators are flagged", () => {
    const result = lex("1 2.5 0xFF 1_000 42n 0b101 0o17 1e3 .5", "t.ts");
    expect(result.diagnostics).toEqual([]);
    const numbers = result.tokens.filter((t) => t.kind === "number");
    expect(numbers.map((t) => t.numeric)).toEqual([
      { isFloat: false, isBigInt: false, base: "decimal" },
      { isFloat: true, isBigInt: false, base: "decimal" },
      { isFloat: false, isBigInt: false, base: "hex" },
      { isFloat: false, isBigInt: false, base: "decimal" },
      { isFloat: false, isBigInt: true, base: "decimal" },
      { isFloat: false, isBigInt: false, base: "binary" },
      { isFloat: false, isBigInt: false, base: "octal" },
      { isFloat: true, isBigInt: false, base: "decimal" },
      { isFloat: true, isBigInt: false, base: "decimal" },
    ]);
  });

  test("member access after an integer literal still lexes", () => {
    expect(texts("a[1].b")).toEqual(["a", "[", "1", "]", ".", "b"]);
  });
});

describe("spans", () => {
  test("line, column and offset are 1-based / 0-based as specified", () => {
    const result = lex("const x = 1;\n  foo(2);", "t.ts");
    const foo = result.tokens.find((t) => t.text === "foo")!;
    expect(foo.span).toMatchObject({ file: "t.ts", line: 2, col: 3, offset: 15, endOffset: 18 });
  });

  test("every token carries an end offset", () => {
    for (const token of lex("a + b.c(1, `x`); // c\n/** d */ e", "t.ts").tokens) {
      expect(token.span.endOffset).toBeGreaterThanOrEqual(token.span.offset);
      expect(token.span.endOffset! - token.span.offset).toBe(token.text.length);
    }
  });
});
