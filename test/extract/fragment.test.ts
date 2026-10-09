/**
 * Milestone 5: the fragment checker on the acceptance examples.
 *
 * `examples/fail/rejected.ts` has one annotated function per rejected construct, each with a
 * comment naming the diagnostic.  Every one must produce exactly one located `fragment`
 * error at the construct; every function in `examples/pass` must check with zero diagnostics.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { extractFile } from "../../src/extract/fragment";
import type { Diagnostic } from "../../src/diagnostics";

const repoRoot = resolve(import.meta.dir, "../..");

function extract(relative: string) {
  const path = resolve(repoRoot, relative);
  return extractFile(path, readFileSync(path, "utf8"));
}

const PASS_FILES = [
  "clamp.ts",
  "abs.ts",
  "safeGet.ts",
  "concat.ts",
  "take.ts",
  "binarySearch.ts",
  "sumTo.ts",
  "shape.ts",
  "useClamp.ts",
];

function errors(diagnostics: readonly Diagnostic[]): Diagnostic[] {
  return diagnostics.filter((d) => d.severity === "error");
}

describe("examples/pass", () => {
  for (const file of PASS_FILES) {
    test(`${file} checks with zero diagnostics`, () => {
      const ir = extract(`examples/pass/${file}`);
      expect(ir.diagnostics.map((d) => `${d.kind}: ${d.message}`)).toEqual([]);
      expect(ir.functions.length).toBeGreaterThan(0);
    });
  }

  test("the union alias of shape.ts is mapped to a nested Sum of Sigma records", () => {
    const ir = extract("examples/pass/shape.ts");
    expect(ir.unions).toHaveLength(1);
    const union = ir.unions[0]!;
    expect(union.name).toBe("Shape");
    expect(union.discriminant).toBe("kind");
    expect(union.variants.map((v) => v.tag)).toEqual(["square", "rect"]);
    expect(union.variants[0]!.fields.map((f) => f.name)).toEqual(["side"]);
    expect(union.variants[1]!.fields.map((f) => f.name)).toEqual(["w", "h"]);
    // A `number` field contributes its value and an `InRange` proof component.
    expect(union.variants[0]!.fields[0]!.path).toEqual([0]);
    expect(union.variants[0]!.fields[0]!.inRangePath).toEqual([1, 0]);
  });
});

describe("examples/fail/rejected.ts", () => {
  const ir = extract("examples/fail/rejected.ts");
  const all = errors(ir.diagnostics);

  /** The single error whose message mentions `needle`. */
  function onlyError(needle: string): Diagnostic {
    const matching = all.filter((d) => d.message.includes(needle));
    expect(matching).toHaveLength(1);
    const diagnostic = matching[0]!;
    expect(diagnostic.kind).toBe("fragment");
    expect(diagnostic.severity).toBe("error");
    expect(diagnostic.span.file.endsWith("rejected.ts")).toBe(true);
    expect(diagnostic.span.line).toBeGreaterThan(0);
    expect(diagnostic.span.col).toBeGreaterThan(0);
    return diagnostic;
  }

  test("`any` is rejected at the annotation", () => {
    const d = onlyError("`any` is not an accepted type");
    expect(d.span.line).toBe(11);
  });

  test("`as` is rejected at the cast", () => {
    const d = onlyError("`as` casts are not allowed");
    expect(d.span.line).toBe(20);
  });

  test("mutating a parameter is rejected at the assignment", () => {
    const d = onlyError("mutating the parameter");
    expect(d.span.line).toBe(29);
  });

  test("plain `/` is rejected at the operator", () => {
    const d = onlyError("`/` is only allowed");
    expect(d.span.line).toBe(39);
  });

  test("`throw` is rejected at the statement", () => {
    const d = onlyError("`throw` is not allowed");
    expect(d.span.line).toBe(47);
  });

  test("a float literal is rejected at the literal", () => {
    const d = onlyError("float literals are not allowed");
    expect(d.span.line).toBe(55);
  });

  test("`this` is rejected at the expression", () => {
    const d = onlyError("`this` is not allowed");
    expect(d.span.line).toBe(63);
  });

  test("`%` is rejected at the operator", () => {
    const d = onlyError("`%` is not allowed");
    expect(d.span.line).toBe(72);
  });

  test("every rejected function has exactly one error", () => {
    for (const fn of ir.functions) {
      const inside = all.filter(
        (d) => d.span.offset >= fn.span.offset && d.span.offset <= (fn.span.endOffset ?? fn.span.offset),
      );
      expect({ fn: fn.name, errors: inside.length }).toEqual({ fn: fn.name, errors: 1 });
    }
    expect(all).toHaveLength(ir.functions.length);
  });
});

describe("fragment rejections", () => {
  function oneError(source: string, needle: string): Diagnostic {
    const ir = extractFile("synthetic.ts", source);
    const matching = ir.diagnostics.filter((d) => d.message.includes(needle));
    expect(matching.map((d) => d.message)).toHaveLength(1);
    const diagnostic = matching[0]!;
    expect(diagnostic.kind).toBe("fragment");
    return diagnostic;
  }

  const annotated = (body: string, params = "x: number", ret = "number", tags = "@post result >= 0") =>
    `/**\n * ${tags}\n */\nexport function f(${params}): ${ret} {\n${body}\n}\n`;

  test("`unknown` is rejected", () => {
    oneError(annotated("  return 1;", "x: unknown"), "`unknown` is not an accepted type");
  });

  test("a non-null assertion is rejected", () => {
    oneError(annotated("  return x!;"), "non-null assertions");
  });

  test("`==` and `!=` are rejected", () => {
    oneError(annotated("  if (x == 1) return 1;\n  return 2;"), "`==` is not allowed");
    oneError(annotated("  if (x != 1) return 1;\n  return 2;"), "`!=` is not allowed");
  });

  test("bitwise operators are rejected", () => {
    oneError(annotated("  return x & 1;"), "bitwise operator `&`");
    oneError(annotated("  return x << 1;"), "bitwise operator `<<`");
  });

  test("arrow functions and closures are rejected", () => {
    oneError(annotated("  return ((y: number) => y)(x);"), "arrow functions and closures");
  });

  test("optional chaining, spread outside an array literal, and `new` are rejected", () => {
    oneError(annotated("  return x?.toString();", "x: number"), "optional chaining");
    oneError(annotated("  return f2(...x);"), "spread (`...`) is only allowed inside an array literal");
    oneError(annotated("  return new Date().getTime();"), "`new` is not allowed");
  });

  test("`await`, `async` and generators are rejected", () => {
    oneError(annotated("  return await x;"), "`await` is not allowed");
    oneError(
      `/**\n * @post result >= 0\n */\nexport async function f(x: number): Promise<number> {\n  return x;\n}\n`,
      "Promise<number>",
    );
    oneError(
      `/**\n * @post result >= 0\n */\nexport function* f(x: number): number {\n  yield x;\n}\n`,
      "`yield` is not allowed",
    );
  });

  test("statements outside the fragment are rejected", () => {
    oneError(annotated("  try {\n    return x;\n  } catch {\n    return 0;\n  }"), "`try statement` is not allowed");
    oneError(annotated("  throw x;"), "`throw` is not allowed");
    oneError(annotated("  class C {}\n  return x;"), "`class declaration` is not allowed");
    oneError(annotated("  for (const y of [1]) { return y; }\n  return x;"), "for…of");
    oneError(annotated("  do {\n    return x;\n  } while (false);"), "do/while");
  });

  test("a missing parameter or return annotation is rejected", () => {
    oneError(annotated("  return 1;", "x"), "needs an explicit type annotation");
    oneError(
      `/**\n * @post result >= 0\n */\nexport function f(x: number) {\n  return x;\n}\n`,
      "needs an explicit return type annotation",
    );
  });

  test("`boolean` is allowed only as a condition type", () => {
    oneError(annotated("  return x;", "x: boolean"), "`boolean` is only allowed as the type of a condition");
  });

  test("a mutable array parameter and array mutation are rejected", () => {
    oneError(annotated("  return a[0];", "a: number[]"), "must be `readonly T[]`");
    oneError(
      annotated("  a.push(1);\n  return 1;", "a: readonly number[]"),
      "array mutation (`push`)",
    );
    oneError(
      annotated("  a[0] = 1;\n  return 1;", "a: readonly number[]"),
      "array mutation",
    );
  });

  test("a recursive type alias is rejected", () => {
    const source =
      'type Loop = { readonly kind: "a"; readonly next: Loop };\n' +
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return x;\n}\n";
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics.some((d) => d.message.includes("is recursive; recursive types are not allowed"))).toBe(
      true,
    );
  });

  test("a non-`number` variant field is rejected with a location", () => {
    const source =
      'type T = { readonly k: "a"; readonly v: string } | { readonly k: "b"; readonly v: number };\n' +
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return x;\n}\n";
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics.some((d) => d.message.includes("only `number` fields are supported"))).toBe(true);
  });

  test("a union with more than two variants is rejected", () => {
    const source =
      'type T = { readonly k: "a" } | { readonly k: "b" } | { readonly k: "c" };\n' +
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return x;\n}\n";
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics.some((d) => d.message.includes("more than two variants"))).toBe(true);
  });

  test("a variant without a shared string-literal discriminant is rejected", () => {
    const source =
      "type T = { readonly a: number } | { readonly b: number };\n" +
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return x;\n}\n";
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics.some((d) => d.message.includes("string-literal discriminant"))).toBe(true);
  });

  test("a call to an unverified function is rejected", () => {
    const source =
      "/**\n * @post result >= 0\n */\nexport function f(x: number): number {\n  return g(x);\n}\n" +
      "function g(x: number): number {\n  return x;\n}\n";
    oneError(source, "is not a verified function");
  });

  test("unresolved names are located", () => {
    const diagnostic = oneError(annotated("  return y + 1;"), "unresolved name `y`");
    expect(diagnostic.span.line).toBe(5);
    expect(diagnostic.span.col).toBe(10);
  });
});

describe("narrowing", () => {
  const withShape = (body: string, ret = "number", tags = "@post result >= 0") =>
    `type Shape =\n` +
    `  | { readonly kind: "square"; readonly side: number }\n` +
    `  | { readonly kind: "rect"; readonly w: number; readonly h: number };\n` +
    `/**\n * ${tags}\n */\nexport function f(s: Shape): ${ret} {\n${body}\n}\n`;

  test("`if` on the discriminant narrows field access", () => {
    const ir = extractFile(
      "synthetic.ts",
      withShape('  if (s.kind === "square") {\n    return s.side;\n  } else {\n    return s.w;\n  }'),
    );
    expect(ir.diagnostics).toEqual([]);
  });

  test("`&&` narrows the right operand", () => {
    const ir = extractFile(
      "synthetic.ts",
      withShape('  if (s.kind === "square" && s.side > 0) {\n    return s.side;\n  }\n  return 0;'),
    );
    expect(ir.diagnostics).toEqual([]);
  });

  test("a ternary narrows both branches", () => {
    const ir = extractFile(
      "synthetic.ts",
      withShape('  return s.kind === "square" ? s.side : s.w + s.h;'),
    );
    expect(ir.diagnostics).toEqual([]);
  });

  test("`switch` narrows each case", () => {
    const ir = extractFile(
      "synthetic.ts",
      withShape(
        '  switch (s.kind) {\n    case "square":\n      return s.side;\n    case "rect":\n      return s.w + s.h;\n  }',
      ),
    );
    expect(ir.diagnostics).toEqual([]);
  });

  test("a missing case, a `default` and a fall-through case are rejected", () => {
    expect(
      extractFile(
        "synthetic.ts",
        withShape('  switch (s.kind) {\n    case "square":\n      return s.side;\n  }'),
      ).diagnostics.some((d) => d.message.includes("must cover the variant")),
    ).toBe(true);
    expect(
      extractFile(
        "synthetic.ts",
        withShape(
          '  switch (s.kind) {\n    case "square":\n      return s.side;\n    default:\n      return 0;\n  }',
        ),
      ).diagnostics.some((d) => d.message.includes("`default` case is not allowed")),
    ).toBe(true);
    expect(
      extractFile(
        "synthetic.ts",
        withShape(
          '  switch (s.kind) {\n    case "square":\n      const t = s.side;\n    case "rect":\n      return s.w;\n  }',
        ),
      ).diagnostics.some((d) => d.message.includes("must end with `return`")),
    ).toBe(true);
  });

  test("field access without narrowing is rejected with a location", () => {
    const ir = extractFile("synthetic.ts", withShape("  return s.side;"));
    const errors = ir.diagnostics.filter((d) => d.message.includes("needs a discriminant narrowing"));
    expect(errors).toHaveLength(1);
    expect(errors[0]!.span.line).toBe(8);
  });

  test("a lowered loop still needs `@invariant` and `@decreases`", () => {
    const source =
      "/**\n * @post result >= 0\n */\nexport function f(n: number): number {\n" +
      "  let i = 0;\n  while (i < n) {\n    i = i + 1;\n  }\n  return i;\n}\n";
    const ir = extractFile("synthetic.ts", source);
    expect(ir.diagnostics.some((d) => d.message.includes("`@invariant`"))).toBe(true);
    expect(ir.diagnostics.some((d) => d.message.includes("`@decreases`"))).toBe(true);
  });
});

describe("determinism", () => {
  test("diagnostics come back sorted and without duplicates", () => {
    const source =
      "/**\n * @post result >= 0\n */\nexport function f(x: any): number {\n  return this;\n}\n";
    const first = extractFile("synthetic.ts", source).diagnostics.map((d) => `${d.span.offset}:${d.message}`);
    const second = extractFile("synthetic.ts", source).diagnostics.map((d) => `${d.span.offset}:${d.message}`);
    expect(first).toEqual(second);
    expect([...first].sort()).toEqual(first);
  });
});
