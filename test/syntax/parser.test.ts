/**
 * Parser tests (section 9.2): precedence and associativity of every accepted
 * operator, nested ternaries, `switch` forms, loops with JSDoc, top-level
 * skipping, recovery, type aliases and imports.
 */
import { describe, expect, test } from "bun:test";
import type * as A from "../../src/syntax/ast";
import { parseFile } from "../../src/syntax/parser";
import { printExpr, printFunction } from "../../src/syntax/print";
import { sameParse } from "../../src/syntax/crosscheck";

function parseBody(body: string, opts?: { includeUnannotated?: boolean }): {
  fn: A.FnDecl;
  source: string;
  diagnostics: ReturnType<typeof parseFile>["diagnostics"];
} {
  const source = `/** @post result === 0 */\nexport function f(a: number, b: number, c: number): number {\n${body}\n}\n`;
  const file = parseFile("t.ts", source, opts);
  const fn = file.functions[0]!;
  return { fn, source, diagnostics: file.diagnostics };
}

function firstExpr(body: string): A.Expr {
  const { fn } = parseBody(body);
  const statement = fn.body.body[0]!;
  if (statement.kind !== "Return" || statement.argument === null) {
    throw new Error("expected a `return <expr>` statement");
  }
  return statement.argument;
}

describe("operator coverage", () => {
  const BINARY = [
    "**",
    "*",
    "/",
    "%",
    "+",
    "-",
    "<<",
    ">>",
    ">>>",
    "<",
    "<=",
    ">",
    ">=",
    "instanceof",
    "in",
    "==",
    "!=",
    "===",
    "!==",
    "&",
    "^",
    "|",
  ];
  for (const op of BINARY) {
    test(`binary \`${op}\` produces a Binary node`, () => {
      const expr = firstExpr(`return a ${op} b;`);
      expect(expr.kind).toBe("Binary");
      expect(String((expr as A.BinaryExpr).op)).toBe(op);
    });
  }

  for (const op of ["&&", "||", "??"]) {
    test(`logical \`${op}\` produces a Logical node`, () => {
      const expr = firstExpr(`return a ${op} b;`);
      expect(expr.kind).toBe("Logical");
      expect(String((expr as A.LogicalExpr).op)).toBe(op);
    });
  }

  const ASSIGN = [
    "=",
    "+=",
    "-=",
    "*=",
    "/=",
    "%=",
    "**=",
    "<<=",
    ">>=",
    ">>>=",
    "&=",
    "|=",
    "^=",
    "&&=",
    "||=",
    "??=",
  ];
  for (const op of ASSIGN) {
    test(`assignment \`${op}\` produces an Assign node`, () => {
      const expr = firstExpr(`return a ${op} b;`);
      expect(expr.kind).toBe("Assign");
      expect(String((expr as A.AssignExpr).op)).toBe(op);
    });
  }

  for (const op of ["-", "+", "!", "~"]) {
    test(`unary \`${op}\` produces a Unary node`, () => {
      const expr = firstExpr(`return ${op}a;`);
      expect(expr.kind).toBe("Unary");
      expect(String((expr as A.UnaryExpr).op)).toBe(op);
    });
  }

  for (const op of ["typeof", "void", "delete"]) {
    test(`unary \`${op}\` produces a Unary node`, () => {
      const expr = firstExpr(`return ${op} a;`);
      expect(expr.kind).toBe("Unary");
      expect(String((expr as A.UnaryExpr).op)).toBe(op);
    });
  }

  test("await and yield parse inside async / generator functions and cross-check", () => {
    const asyncSource = `/** @post result === 0 */\nexport async function f(a: number): Promise<number> {\n  const x = await g(a);\n  return x;\n}\n`;
    const asyncParsed = parseFile("async.ts", asyncSource);
    expect(asyncParsed.diagnostics).toEqual([]);
    const asyncFn = asyncParsed.functions[0]!;
    expect(asyncFn.async).toBe(true);
    expect((asyncFn.body.body[0] as A.VarDeclStmt).declarations[0]!.init!.kind).toBe("Await");
    expect(sameParse(asyncFn.text, printFunction(asyncFn))).toBe(true);

    const genSource = `/** @decreases n */\nexport function* gen(n: number): Iterable<number> {\n  yield n;\n  yield* other(n);\n}\n`;
    const genParsed = parseFile("gen.ts", genSource);
    expect(genParsed.diagnostics).toEqual([]);
    const genFn = genParsed.functions[0]!;
    expect(genFn.generator).toBe(true);
    expect((genFn.body.body[0] as A.ExprStmt).expr.kind).toBe("Yield");
    expect((genFn.body.body[1] as A.ExprStmt).expr).toMatchObject({ kind: "Yield", delegate: true });
    expect(sameParse(genFn.text, printFunction(genFn))).toBe(true);
  });

  test("prefix and postfix update", () => {
    const prefix = firstExpr("return ++a;") as A.UpdateExpr;
    expect(prefix).toMatchObject({ kind: "Update", op: "++", prefix: true });
    const postfix = firstExpr("return a--;") as A.UpdateExpr;
    expect(postfix).toMatchObject({ kind: "Update", op: "--", prefix: false });
  });
});

describe("precedence and associativity", () => {
  const CASES: Array<[string, string]> = [
    ["a + b - c", "((a + b) - c)"],
    ["a - b - c", "((a - b) - c)"],
    ["a - (b - c)", "(a - (b - c))"],
    ["a * b / c % d", "(((a * b) / c) % d)"],
    ["a + b * c", "(a + (b * c))"],
    ["(a + b) * c", "((a + b) * c)"],
    ["a ** b ** c", "(a ** (b ** c))"],
    ["(a ** b) ** c", "((a ** b) ** c)"],
    ["a << b >> c >>> d", "(((a << b) >> c) >>> d)"],
    ["a + b << c", "((a + b) << c)"],
    ["a < b === c", "((a < b) === c)"],
    ["a === b !== c", "((a === b) !== c)"],
    ["a & b | c ^ d", "((a & b) | (c ^ d))"],
    ["a && b || c", "((a && b) || c)"],
    ["a || b && c", "(a || (b && c))"],
    ["a ?? b", "(a ?? b)"],
    ["a === b ? c : d", "((a === b) ? c : d)"],
    ["a ? b : c ? d : e", "(a ? b : (c ? d : e))"],
    ["a ? b ? c : d : e", "(a ? (b ? c : d) : e)"],
    ["-a + +b", "((-a) + (+b))"],
    ["!a && ~b", "((!a) && (~b))"],
    ['typeof a === "number"', '((typeof a) === "number")'],
    ["void a", "(void a)"],
    ["delete a.b", "(delete (a).b)"],
    ["a = b = c", "(a = (b = c))"],
    ["a += b", "(a += b)"],
    ["a &&= b", "(a &&= b)"],
    ["a++ + ++b", "((a++) + (++b))"],
    ["a.b.c", "((a).b).c"],
    ["a[b][c]", "((a)[b])[c]"],
    ["f(a, b)(c)", "((f)(a, b))(c)"],
    ["a?.b", "(a)?.b"],
    ["a?.[a]", "(a)?.[a]"],
    ["a?.()", "(a)?.()"],
    ["a!.b", "((a!)).b"],
    ["new C(1)", "new (C)(1)"],
    ["new C", "new (C)"],
    ["new a.b(1)", "new ((a).b)(1)"],
    ["a as number", "(a as number)"],
    ["[...a, ...b]", "[...a, ...b]"],
    ['{ kind: "x", n: 1 }', '{ kind: "x", n: 1 }'],
    ["a.slice(0, b)", "((a).slice)(0, b)"],
    ["(a) => a", "((a) => a)"],
    ["a => a + b", "((a) => (a + b))"],
    ["(a, b)", "(a, b)"],
    ["`x${a}y`", "`x${a}y`"],
    ["a!", "(a!)"],
    ["1.5", "1.5"],
    ["0xFF", "0xFF"],
    ["1_000n", "1_000n"],
    ['"s"', '"s"'],
    ["true", "true"],
    ["this", "this"],
    ["[1, 2]", "[1, 2]"],
    ["{}", "{}"],
    ["f`x`", "f`x`"],
  ];

  for (const [source, expected] of CASES) {
    test(`\`${source}\` prints as \`${expected}\``, () => {
      const { fn } = parseBody(`return ${source};`);
      const statement = fn.body.body[0]!;
      if (statement.kind !== "Return" || statement.argument === null) throw new Error("no return");
      expect(printExpr(statement.argument)).toBe(expected);
      expect(sameParse(fn.text, printFunction(fn))).toBe(true);
      expect(parseBody(`return ${source};`).diagnostics).toEqual([]);
    });
  }
});

describe("statements", () => {
  test("if / else if / else chain", () => {
    const { fn, diagnostics } = parseBody(`  if (a < b) return a;
  else if (a > b) return b;
  else return c;`);
    expect(diagnostics).toEqual([]);
    const ifStmt = fn.body.body[0] as A.IfStmt;
    expect(ifStmt.kind).toBe("If");
    expect(ifStmt.alternate!.kind).toBe("If");
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });

  test("braced and unbraced if bodies are both preserved", () => {
    const unbraced = parseBody("  if (a < b) return a;\n  return c;");
    expect((unbraced.fn.body.body[0] as A.IfStmt).then.kind).toBe("Return");
    expect(sameParse(unbraced.fn.text, printFunction(unbraced.fn))).toBe(true);
    const braced = parseBody("  if (a < b) { return a; }\n  return c;");
    expect((braced.fn.body.body[0] as A.IfStmt).then.kind).toBe("Block");
    expect(sameParse(braced.fn.text, printFunction(braced.fn))).toBe(true);
  });

  test("const and let declarations keep their type annotations verbatim", () => {
    const { fn, diagnostics } = parseBody("  const x: number = a + 1;\n  let y = x;\n  return y;");
    expect(diagnostics).toEqual([]);
    const decl = fn.body.body[0] as A.VarDeclStmt;
    expect(decl.kind).toBe("VarDecl");
    expect(decl.declKind).toBe("const");
    expect(decl.declarations[0]).toMatchObject({ name: "x", typeText: "number" });
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });

  test("switch forms: plain, grouped cases, default and braced bodies", () => {
    const { fn, diagnostics } = parseBody(`  switch (a) {
    case 0:
    case 1:
      return a;
    case 2: {
      return b;
    }
    default:
      return c;
  }`);
    expect(diagnostics).toEqual([]);
    const switchStmt = fn.body.body[0] as A.SwitchStmt;
    expect(switchStmt.kind).toBe("Switch");
    expect(switchStmt.cases.map((c) => (c.test === null ? "default" : printExpr(c.test)))).toEqual([
      "0",
      "1",
      "2",
      "default",
    ]);
    expect(switchStmt.cases[0]!.body).toEqual([]);
    expect(switchStmt.cases[2]!.braced).toBe(true);
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });

  test("while and for carry their loop JSDoc", () => {
    const { fn, diagnostics } = parseBody(`  let i = 0;
  /**
   * @invariant 0 <= i && i <= a
   * @decreases a - i
   */
  while (i < a) {
    i = i + 1;
  }
  /**
   * @invariant i === i
   * @decreases a - i
   */
  for (let j = 0; j < a; j++) {
    i = i + 1;
  }
  return i;`);
    expect(diagnostics).toEqual([]);
    const whileStmt = fn.body.body[1] as A.WhileStmt;
    expect(whileStmt.kind).toBe("While");
    expect(whileStmt.jsdoc!.tags.map((t) => `${t.name}:${t.text}`)).toEqual([
      "invariant:0 <= i && i <= a",
      "decreases:a - i",
    ]);
    const forStmt = fn.body.body[2] as A.ForStmt;
    expect(forStmt.kind).toBe("For");
    expect(forStmt.jsdoc!.tags.map((t) => t.name)).toEqual(["invariant", "decreases"]);
    expect(forStmt.init!.kind).toBe("VarDecl");
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });

  test("for headers with empty parts still parse", () => {
    const { fn, diagnostics } = parseBody("  for (;;) { return a; }");
    expect(diagnostics).toEqual([]);
    const forStmt = fn.body.body[0] as A.ForStmt;
    expect([forStmt.init, forStmt.test, forStmt.update]).toEqual([null, null, null]);
  });

  test("a loop JSDoc with spec tags that does not precede a loop is a parse error", () => {
    const { diagnostics } = parseBody(`  /**
   * @invariant i === i
   */
  const x = a;
  return x;`);
    expect(diagnostics.map((d) => d.message)).toEqual([
      "`@invariant`/`@decreases` must annotate a `while` or `for` loop",
    ]);
  });

  test("switch statement forms in a function with a JSDoc block still cross-check", () => {
    const { fn } = parseBody(`  switch (a) {
    case 0:
      return 1;
    default:
      return 2;
  }`);
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });
});

describe("rejected constructs are parsed, not rejected", () => {
  test("`any`, `unknown`, `this`, `/`, `%`, floats, `as`, `new`, `await`, arrows, `!`", () => {
    const { fn, diagnostics } = parseBody(`  const x: any = a;
  const y: unknown = b;
  const z = this;
  const w = a / b;
  const v = a % b;
  const u = 1.5;
  const t = a as number;
  const s = new Date();
  const r = await a;
  const q = (p: number) => p;
  const n = a!;
  return c;`);
    expect(diagnostics).toEqual([]);
    const spans = fn.body.body.map((s) => s.span);
    expect(spans.length).toBe(12);
    const declTypes = fn.body.body
      .filter((s): s is A.VarDeclStmt => s.kind === "VarDecl")
      .map((s) => s.declarations[0]!.typeAnn?.kind);
    expect(declTypes.slice(0, 2)).toEqual(["AnyType", "UnknownType"]);
    const inits = fn.body.body
      .filter((s): s is A.VarDeclStmt => s.kind === "VarDecl")
      .map((s) => s.declarations[0]!.init);
    expect(inits[2]!.kind).toBe("This");
    expect(inits[3]).toMatchObject({ kind: "Binary", op: "/" });
    expect(inits[4]).toMatchObject({ kind: "Binary", op: "%" });
    expect(inits[5]).toMatchObject({ kind: "Lit", lit: "float" });
    expect(inits[6]!.kind).toBe("As");
    expect(inits[7]!.kind).toBe("New");
    expect(inits[8]!.kind).toBe("Await");
    expect(inits[9]!.kind).toBe("Arrow");
    expect(inits[10]!.kind).toBe("NonNull");
  });

  test("optional chaining, spread, templates and throw produce nodes", () => {
    const { fn, diagnostics } = parseBody(`  const x = a?.b;
  const y = a?.b?.(c);
  const z = [...a];
  const t = \`v=\${a}\`;
  throw new Error("no");
  return c;`);
    expect(diagnostics).toEqual([]);
    const inits = fn.body.body
      .filter((s): s is A.VarDeclStmt => s.kind === "VarDecl")
      .map((s) => s.declarations[0]!.init);
    expect(inits[0]).toMatchObject({ kind: "Member", optional: true });
    expect(inits[1]!.kind).toBe("Call");
    expect(inits[2]).toMatchObject({ kind: "ArrayLit" });
    expect(inits[3]!.kind).toBe("Template");
    expect(fn.body.body[4]!.kind).toBe("Throw");
  });

  test("a float literal in a return keeps its raw text and value", () => {
    const expr = firstExpr("return 1.5;") as A.Lit;
    expect(expr).toMatchObject({ kind: "Lit", lit: "float", raw: "1.5", value: 1.5 });
    const hex = firstExpr("return 0xFF;") as A.Lit;
    expect(hex).toMatchObject({ lit: "hex", value: 255n });
    const big = firstExpr("return 42n;") as A.Lit;
    expect(big).toMatchObject({ lit: "bigint", value: 42n });
    const str = firstExpr('return "sq";') as A.Lit;
    expect(str).toMatchObject({ lit: "string", value: "sq" });
  });

  test("unsupported statements are recognised verbatim so milestone 5 can name them", () => {
    const { fn, diagnostics } = parseBody(`  try { return a; } catch { return b; }`);
    expect(diagnostics).toEqual([]);
    const stmt = fn.body.body[0] as A.UnsupportedStmt;
    expect(stmt.kind).toBe("Unsupported");
    expect(stmt.what).toContain("try");
    expect(stmt.text).toBe("try { return a; } catch { return b; }");
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });

  test("a nested function declaration is an Unsupported statement", () => {
    const { fn, diagnostics } = parseBody(`  function g(x: number): number { return x; }
  return g(a);`);
    expect(diagnostics).toEqual([]);
    expect((fn.body.body[0] as A.UnsupportedStmt).what).toContain("nested function");
    expect(sameParse(fn.text, printFunction(fn))).toBe(true);
  });
});

describe("top-level skipping", () => {
  const source = `import { readFileSync } from "node:fs";
import "./side-effect";

const helper = (x: number) => x + 1;
class K { m() { return 1; } }
interface I { a: number }
for (const x of [1, 2]) console.log(x);
console.log("done")
/** @post result >= 0 */
export function annotated(x: number): number {
  return helper(x);
}
function plain(x: number): number { return x; }
`;
  const parsed = parseFile("skip.ts", source);

  test("only the annotated function is fully parsed", () => {
    expect(parsed.functions.map((f) => f.name)).toEqual(["annotated"]);
    expect(parsed.diagnostics).toEqual([]);
  });

  test("all imports are recorded", () => {
    expect(parsed.imports.map((i) => [i.specifier, i.relative])).toEqual([
      ["node:fs", false],
      ["./side-effect", true],
    ]);
    expect(parsed.imports[0]!.bindings).toEqual([
      { imported: "readFileSync", local: "readFileSync", typeOnly: false, span: expect.anything() },
    ]);
  });

  test("the annotated function's span and text cover the declaration", () => {
    const fn = parsed.functions[0]!;
    expect(fn.exported).toBe(true);
    expect(source.slice(fn.span.offset, fn.span.endOffset)).toBe(fn.text);
    expect(fn.text.startsWith("export function annotated")).toBe(true);
    expect(fn.text.endsWith("}")).toBe(true);
  });

  test("includeUnannotated also parses plain functions", () => {
    const all = parseFile("skip.ts", source, { includeUnannotated: true });
    expect(all.functions.map((f) => f.name)).toEqual(["annotated", "plain"]);
  });
});

describe("imports", () => {
  test("named, aliased, default, namespace and type-only bindings", () => {
    const parsed = parseFile(
      "i.ts",
      `import def, { a, b as c, type T } from "./m";
import * as ns from "../n";
import type { X } from "./x";
import "./side";
`,
    );
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.imports.map((i) => i.specifier)).toEqual(["./m", "../n", "./x", "./side"]);
    expect(parsed.imports[0]!.defaultImport!.name).toBe("def");
    expect(parsed.imports[0]!.bindings.map((b) => [b.imported, b.local, b.typeOnly])).toEqual([
      ["a", "a", false],
      ["b", "c", false],
      ["T", "T", true],
    ]);
    expect(parsed.imports[1]!.namespaceImport!.name).toBe("ns");
    expect(parsed.imports[2]!.typeOnly).toBe(true);
    expect(parsed.imports[3]!.bindings).toEqual([]);
    expect(parsed.imports.every((i) => i.relative)).toBe(true);
  });
});

describe("unmodelled type syntax", () => {
  test("a union return type on an unannotated function does not lose the parser's place", () => {
    const source = `function at(args: readonly number[], index: number): number | undefined {
  return index < args.length ? args[index] : undefined;
}
/** @post result >= 0 */
export function annotated(x: number): number {
  return x;
}
`;
    const parsed = parseFile("union.ts", source);
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.functions.map((f) => f.name)).toEqual(["annotated"]);
  });

  test("a type-predicate return type is kept verbatim and the body still parses", () => {
    const source = `export function isNumber(value: string | number): value is number {
  return typeof value === "number";
}
/** @post result >= 0 */
export function annotated(x: number): number {
  return x;
}
`;
    const parsed = parseFile("predicate.ts", source);
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.functions.map((f) => f.name)).toEqual(["annotated"]);
  });

  test("an annotated function's union-typed parameter becomes a verbatim OtherType", () => {
    const { fn, diagnostics } = parseBody("  return a;");
    expect(diagnostics).toEqual([]);
    void fn;
    const source = "/** @post result >= 0 */\nexport function f(x: number | undefined): number {\n  return 0;\n}\n";
    const parsed = parseFile("u.ts", source);
    expect(parsed.diagnostics).toEqual([]);
    const param = parsed.functions[0]!.params[0]!;
    expect(param.typeAnn).toMatchObject({ kind: "OtherType", text: "number | undefined" });
    expect(param.typeText).toBe("number | undefined");
  });

  test("type aliases made of string literals and generics parse without diagnostics", () => {
    const parsed = parseFile(
      "kinds.ts",
      `type Kind = "a" | "b";
type Bag = Record<string, number>;
type Box<T> = { readonly value: T };
type Either = Box<number> | Box<string>;
type Keys = keyof Bag;
`,
    );
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.typeAliases.map((a) => a.name)).toEqual(["Kind", "Bag", "Box", "Either", "Keys"]);
    expect(parsed.typeAliases[0]!.variants.map((v) => v.text)).toEqual(['"a"', '"b"']);
    expect(parsed.typeAliases[3]!.variants.map((v) => v.text)).toEqual(["Box<number>", "Box<string>"]);
  });

  test("a signature-level failure in an annotated function is reported once and skipped", () => {
    const source = "/** @post result >= 0 */\nexport function f({ a }: { a: number }): number {\n  return a;\n}\n";
    const parsed = parseFile("sig.ts", source);
    expect(parsed.diagnostics.map((d) => d.message)).toEqual([
      "destructuring parameters are not supported",
    ]);
    expect(parsed.diagnostics[0]!.span).toMatchObject({ line: 2, col: 19 });
    expect(parsed.functions).toEqual([]);
  });

  test("the same failure in an unannotated function is not reported", () => {
    const source = `function g({ a }: { a: number }): number { return a; }
/** @post result >= 0 */
export function f(x: number): number { return x; }
`;
    const parsed = parseFile("sig2.ts", source);
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.functions.map((f) => f.name)).toEqual(["f"]);
  });

  test("parseFile never throws, whatever the input", () => {
    const snippets = [
      "}",
      ")",
      "]",
      "/** @pre */",
      "/** @pre x > 0",
      "function f(",
      "type X = |",
      "type X = { a: }",
      "export function f(x: number): number { return a +; }",
      "const s = \"unterminated",
      "const t = `unterminated",
      "/* unterminated",
      "const x = (",
      "export async function",
      "function f() {",
      "switch (x) {",
      "class",
      "for (;;",
      "@decorator class A {}",
      "a?.5:b",
      "#!/usr/bin/env bun\nfunction f() {",
    ];
    for (const snippet of snippets) {
      expect(() => parseFile("weird.ts", snippet)).not.toThrow();
    }
  });
});

describe("type aliases", () => {
  const source = `export type Shape =
  | { readonly kind: "square"; readonly side: number }
  | { readonly kind: "rect"; readonly w: number; readonly h: number };

type Alias = Other | Another;
type Box<T> = { readonly value: T };
`;
  const parsed = parseFile("aliases.ts", source);

  test("all aliases are parsed", () => {
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.typeAliases.map((a) => a.name)).toEqual(["Shape", "Alias", "Box"]);
    expect(parsed.typeAliases[2]!.typeParams.map((p) => p.name)).toEqual(["T"]);
  });

  test("variants keep readonly fields and a string-literal discriminant", () => {
    const shape = parsed.typeAliases[0]!;
    expect(shape.variants.length).toBe(2);
    expect(shape.variants[0]!.fields.map((f) => [f.name, f.readonly, f.typeText])).toEqual([
      ["kind", true, '"square"'],
      ["side", true, "number"],
    ]);
    expect(shape.variants[0]!.discriminant).toMatchObject({ key: "kind", value: "square" });
    expect(shape.variants[1]!.discriminant).toMatchObject({ key: "kind", value: "rect" });
  });

  test("named variants are recorded without fields", () => {
    const alias = parsed.typeAliases[1]!;
    expect(alias.variants.map((v) => [v.name, v.fields.length])).toEqual([
      ["Other", 0],
      ["Another", 0],
    ]);
  });

  test("a `type` alias inside a function body is an unsupported statement", () => {
    const { fn, diagnostics } = parseBody("  type T = number;\n  return a;");
    expect(diagnostics).toEqual([]);
    expect((fn.body.body[0] as A.UnsupportedStmt).what).toContain("type alias");
  });
});

describe("diagnostics and recovery", () => {
  test("several broken statements are all reported, in source order", () => {
    const { diagnostics } = parseBody(`  const { x } = a;
  return b;
  const [y] = c;
  return d;`);
    const messages = diagnostics.map((d) => `${d.span.line}:${d.message}`);
    expect(messages).toEqual([
      "3:destructuring declarations are not supported",
      "5:destructuring declarations are not supported",
    ]);
    for (let i = 1; i < diagnostics.length; i += 1) {
      expect(diagnostics[i]!.span.offset).toBeGreaterThanOrEqual(diagnostics[i - 1]!.span.offset);
    }
  });

  test("an unexpected token gets a located `parse` diagnostic and parsing continues", () => {
    const { fn, diagnostics } = parseBody("  return a +;\n  return b;");
    expect(diagnostics.length).toBeGreaterThanOrEqual(1);
    expect(diagnostics[0]!.kind).toBe("parse");
    expect(diagnostics[0]!.span.line).toBe(3);
    expect(fn.body.body.length).toBeGreaterThanOrEqual(1);
  });

  test("unterminated literals inside a function are located", () => {
    const source = '/** @post result === 0 */\nexport function f(): number {\n  const s = "abc\n  return 1;\n}\n';
    const parsed = parseFile("bad.ts", source);
    expect(parsed.diagnostics.map((d) => d.message)).toEqual([
      "unterminated string literal",
    ]);
    expect(parsed.diagnostics[0]!.span).toMatchObject({ line: 3, col: 13 });
  });

  test("an unannotated function's JSDoc problems are not reported", () => {
    const source = `/**
 * @param
 */
function plain(x: number): number { return x; }
/** @pre x > 0 */
export function annotated(x: number): number { return x; }`;
    const parsed = parseFile("prose.ts", source);
    expect(parsed.diagnostics).toEqual([]);
    expect(parsed.functions.map((f) => f.name)).toEqual(["annotated"]);
  });

  test("an empty spec tag in an annotated function is reported with a location", () => {
    const source = "/**\n * @pre\n */\nexport function f(x: number): number { return x; }\n";
    const parsed = parseFile("empty.ts", source);
    expect(parsed.diagnostics.map((d) => d.message)).toEqual([
      "empty `@pre` tag: expected an expression",
    ]);
    expect(parsed.diagnostics[0]!.span.line).toBe(2);
    expect(parsed.functions.length).toBe(1);
  });
});
