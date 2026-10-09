/**
 * The three defects of the extraction layer that this file pins down:
 *
 * 1. a bare `{ … }` block used to be spliced into the enclosing statement list, so a
 *    `let`/`const` declared in it stayed in scope after the block and the elaborated term
 *    could return a value the JavaScript never produces (`section 4.2` does not accept a
 *    statement-level block at all);
 * 2. a call site checked only the *number* of arguments, so a wrong-typed argument reached
 *    the kernel and surfaced as an `internal` diagnostic or a nonsensical counterexample;
 * 3. a `for (let i = e; c; update)` loop's own `let i` was not in scope for the loop's JSDoc
 *    and its `invariant-init`/`measure-nonneg` obligations were re-checked in the enclosing
 *    environment, where `i` does not exist.
 */
import { describe, expect, test } from "bun:test";
import { extractFile, renderExpr } from "../../src/extract/fragment";

function extract(source: string) {
  return extractFile("synthetic.ts", source);
}

function fragmentErrors(source: string) {
  return extract(source).diagnostics.filter((d) => d.kind === "fragment" && d.severity === "error");
}

describe("1. a statement-level block", () => {
  const shadowParam = `/**
 * @pre x >= 0 && x <= 100
 * @post result === 5
 */
export function f(x: number): number {
  {
    let x = 5;
  }
  return x;
}
`;

  const shadowLet = `/**
 * @pre x >= 0
 * @post result === 5
 */
export function f(x: number): number {
  {
    let y = 5;
  }
  return y;
}
`;

  test("a block shadowing a parameter is rejected at the block, not certified", () => {
    const ir = extract(shadowParam);
    const errors = fragmentErrors(shadowParam);
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("block statement is not allowed");
    // The diagnostic is located at the block itself (`{` on line 6).
    expect(errors[0]!.span.line).toBe(6);
    expect(errors[0]!.span.col).toBe(3);
    expect(errors[0]!.span.offset).toBeGreaterThan(0);
    expect(ir.functions).toHaveLength(1);
  });

  test("a binding declared in a block does not become resolvable after it", () => {
    const errors = fragmentErrors(shadowLet);
    // Exactly one error: the block.  The walk stops there, so the block's `y` is never
    // bound in the enclosing environment (a `return y` after it would be `unresolved`).
    expect(errors.map((d) => d.message)).toEqual([
      expect.stringContaining("block statement is not allowed"),
    ]);
    expect(errors[0]!.span.line).toBe(6);
  });

  test("a nested block inside an `if` branch is rejected too", () => {
    const source = `/**
 * @pre 0 <= x && x <= 100
 * @post result >= 0
 */
export function f(x: number): number {
  if (x > 0) {
    {
      let z = 1;
    }
    return 1;
  }
  return 0;
}
`;
    const errors = fragmentErrors(source);
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("block statement is not allowed");
    expect(errors[0]!.span.line).toBe(7);
  });

  test("the braces of an `if` body are not a statement-level block", () => {
    const source = `/**
 * @pre -100 <= x && x <= 100
 * @post result >= 0
 */
export function f(x: number): number {
  if (x > 0) {
    const z = 1;
    return z;
  }
  return 0;
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("the braces of a loop body are not a statement-level block", () => {
    const source = `/**
 * @pre 0 <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number): number {
  let i = 0;
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  while (i < n) {
    const one = 1;
    acc = acc + one;
    i = i + 1;
  }
  return acc;
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("a `for` loop body with braces is not a statement-level block", () => {
    const source = `/**
 * @pre 0 <= n && n <= 100
 * @post result >= 0
 */
export function f(n: number): number {
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = 0; i < n; i = i + 1) {
    const one = 1;
    acc = acc + one;
  }
  return acc;
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });
});

describe("2. call-site argument types", () => {
  const callee = `/**
 * @pre x >= 0
 * @post result >= 0
 */
export function g(x: number): number {
  return x;
}
`;

  function oneError(source: string) {
    const errors = fragmentErrors(source);
    expect(errors).toHaveLength(1);
    return errors[0]!;
  }

  test("a `readonly number[]` argument to a `number` parameter is rejected", () => {
    const error = oneError(`${callee}/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function f(a: readonly number[]): number {
  return g(a);
}
`);
    expect(error.message).toContain("`g` needs `number` for the parameter `x`");
    expect(error.message).toContain("`a` has type `readonly number[]`");
    // Located at the argument (line 13, column 12), not at the call or the callee.
    expect(error.span.line).toBe(13);
    expect(error.span.col).toBe(12);
  });

  test("a `number` argument to a `readonly number[]` parameter is rejected", () => {
    const error = oneError(`/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function g(a: readonly number[]): number {
  return a.length;
}
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function f(x: number): number {
  return g(x);
}
`);
    expect(error.message).toContain("`g` needs `readonly number[]` for the parameter `a`");
    expect(error.message).toContain("`x` has type `number`");
    expect(error.span.line).toBe(13);
  });

  test("a condition argument to a `number` parameter is rejected", () => {
    const error = oneError(`${callee}/**
 * @post result >= 0
 */
export function f(x: number): number {
  return g(x > 0);
}
`);
    expect(error.message).toContain("`g` needs `number` for the parameter `x`");
    expect(error.message).toContain("has type `boolean`");
  });

  const union = `type U = { readonly kind: "a"; readonly v: number } | { readonly kind: "b"; readonly w: number };
`;

  test("a union argument to a `number` parameter is rejected", () => {
    const error = oneError(`${union}${callee}/**
 * @pre u.kind === "a"
 * @post result >= 0
 */
export function f(u: U): number {
  return g(u);
}
`);
    expect(error.message).toContain("`g` needs `number` for the parameter `x`");
    expect(error.message).toContain("`u` has type `U`");
    expect(error.span.line).toBe(14);
  });

  test("a `number` argument to a union parameter is rejected", () => {
    const error = oneError(`${union}/**
 * @pre u.kind === "a"
 * @post result >= 0
 */
export function g(u: U): number {
  return 0;
}
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function f(x: number): number {
  return g(x);
}
`);
    expect(error.message).toContain("`g` needs `U` for the parameter `u`");
    expect(error.message).toContain("`x` has type `number`");
  });

  test("a `readonly number[]` argument to a `readonly U[]` parameter is rejected", () => {
    const error = oneError(`${union}/**
 * @pre us.length >= 0
 * @post result >= 0
 */
export function g(us: readonly U[]): number {
  return 0;
}
/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function f(a: readonly number[]): number {
  return g(a);
}
`);
    expect(error.message).toContain("`g` needs `readonly U[]` for the parameter `us`");
    expect(error.message).toContain("`a` has type `readonly number[]`");
  });

  test("a `readonly U[]` argument fits a `readonly T[]` parameter", () => {
    const source = `${union}/**
 * @pre a.length <= 4294967295
 * @post result.length === a.length
 */
export function idArr<T>(a: readonly T[]): readonly T[] {
  return [...a];
}
/**
 * @pre us.length <= 4294967295
 * @post result.length === us.length
 */
export function f(us: readonly U[]): readonly U[] {
  return idArr(us);
}
`;
    // A generic element position accepts any accepted element type; instantiating `T` with
    // `U` (and reporting it when it cannot be inferred) is the elaborator's business.
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("a `readonly number[]` argument fits a `readonly T[]` parameter", () => {
    const source = `/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function len<T>(a: readonly T[]): number {
  return a.length;
}
/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function numberLen(a: readonly number[]): number {
  return len(a);
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("a call from a generic function with the same type parameter is accepted", () => {
    const source = `/**
 * @post result >= 0
 */
export function id<T>(x: T): number {
  return 0;
}
/**
 * @post result >= 0
 */
export function f<T>(x: T): number {
  return id(x);
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("an argument type mismatch is reported once per bad argument", () => {
    const errors = fragmentErrors(`${callee}/**
 * @pre a.length >= 0
 * @post result >= 0
 */
export function f(a: readonly number[], b: readonly number[]): number {
  return g(a) + g(b);
}
`);
    expect(errors).toHaveLength(2);
    expect(errors.every((d) => d.message.includes("needs `number`"))).toBe(true);
  });

  test("the right-typed arguments of a vector-taking function still check", () => {
    const source = `/**
 * @pre a.length + b.length <= 4294967295
 * @post result.length === a.length + b.length
 */
export function cat<T>(a: readonly T[], b: readonly T[]): readonly T[] {
  return [...a, ...b];
}
/**
 * @pre a.length + b.length <= 4294967295
 * @post result.length === a.length + b.length
 */
export function use<T>(a: readonly T[], b: readonly T[]): readonly T[] {
  return cat(a, b);
}
`;
    expect(extract(source).diagnostics).toEqual([]);
  });
});

describe("3. a `for` loop's own `let`", () => {
  const canonical = `/**
 * @pre 0 <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number): number {
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = 0; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;

  test("the loop variable is in scope for the loop's own `@invariant`/`@decreases`", () => {
    const ir = extract(canonical);
    expect(ir.diagnostics).toEqual([]);
    const loop = ir.functions[0]!.loops[0]!;
    expect(loop.carried.map((c) => c.name)).toEqual(["acc", "i"]);
    // The spec was checked with `i` as a state component, not re-parsed in the outer scope.
    expect(renderExpr(loop.invariant)).toBe(
      "((((0 <= i) && (i <= n)) && (0 <= acc)) && (acc <= i))",
    );
  });

  test("`invariant-init` substitutes the initial value for the loop variable", () => {
    const ir = extract(canonical);
    const loop = ir.functions[0]!.loops[0]!;
    expect(loop.initSites.map((s) => s.kind)).toEqual(["invariant-init", "measure-nonneg"]);
    // `@invariant 0 <= i && i <= n && …` at `for (let i = 0; …)`: `i` is `0`.
    expect(loop.initSites[0]!.text).toContain("(0 <= 0)");
    expect(loop.initSites[0]!.text).toContain("(0 <= n)");
    // `@decreases n - i` becomes `0 <= (n - 0)`.
    expect(loop.initSites[1]!.text).toBe("(0 <= (n - 0))");
  });

  test("a non-zero initial value is substituted too", () => {
    const source = `/**
 * @pre 2 <= n && n <= 100
 * @post result >= 0
 */
export function f(n: number): number {
  let acc = 0;
  /**
   * @invariant 2 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = 2; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;
    const ir = extract(source);
    expect(ir.diagnostics).toEqual([]);
    const loop = ir.functions[0]!.loops[0]!;
    expect(loop.initSites[0]!.text).toContain("(2 <= 2)");
  });

  test("the loop variable is not in scope after the loop (JavaScript's `let` scope)", () => {
    const source = canonical.replace("  return acc;", "  return i;");
    const errors = fragmentErrors(source);
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("unresolved name `i`");
    // The `return i;` after the loop, exactly where JavaScript throws a ReferenceError.
    expect(errors[0]!.span.line).toBe(14);
  });

  test("an outer variable of the same name is restored after the loop", () => {
    const source = `/**
 * @pre 0 <= n && n <= 100
 * @post result === 7
 */
export function f(n: number): number {
  let i = 7;
  let acc = 0;
  /**
   * @invariant 0 <= j && j <= n && 0 <= acc && acc <= j
   * @decreases n - j
   */
  for (let j = 0; j < n; j = j + 1) {
    acc = acc + 1;
  }
  return i;
}
`;
    // The `for`'s `j` shadows nothing, and the outer `i` is untouched: no diagnostics.
    expect(extract(source).diagnostics).toEqual([]);
  });

  test("a `for` with an empty init keeps the counter of the enclosing scope", () => {
    const source = `/**
 * @pre 0 <= n && n <= 100
 * @post result === n
 */
export function f(n: number): number {
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n
   * @decreases n - i
   */
  for (; i < n; i = i + 1) {
    i = i + 1;
  }
  return i;
}
`;
    // `i` is an ordinary carried `let` here, so it is still in scope after the loop; the
    // body's double increment makes the invariant fail, but that is a post/invariant issue,
    // not an extraction one.
    const errors = fragmentErrors(source);
    expect(errors).toEqual([]);
  });

  test("a counter initialized by a call is rejected with one located error", () => {
    const source = `/**
 * @pre 0 <= x && x <= 10
 * @post result === x
 */
export function start(x: number): number {
  return x;
}
/**
 * @pre 0 <= x && x <= 10 && x <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number, x: number): number {
  let acc = 0;
  /**
   * @invariant x <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = start(x); i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;
    // The loop's start tuple is elaborated before the call's `pre-call` proof exists, so the
    // initializer is outside the fragment: one located `fragment` error, no `internal` one.
    const diagnostics = extract(source).diagnostics;
    expect(diagnostics).toHaveLength(1);
    const error = diagnostics[0]!;
    expect(error.kind).toBe("fragment");
    expect(error.message).toContain("cannot be initialized by an expression whose term needs an obligation proof");
    expect(error.span.line).toBe(18);
    expect(error.span.col).toBe(12);
  });

  test("a counter initialized by an index expression is rejected the same way", () => {
    const source = `/**
 * @pre a.length >= 1 && n <= 100
 * @post result >= 0
 */
export function f(n: number, a: readonly number[]): number {
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (let i = a[0]; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;
    const errors = fragmentErrors(source);
    expect(errors).toHaveLength(1);
    expect(errors[0]!.message).toContain("needs an obligation proof");
    expect(errors[0]!.span.line).toBe(11);
  });

  test("a `let` before the loop is the supported way to start from a call", () => {
    const source = `/**
 * @pre 0 <= x && x <= 10
 * @post result === x
 */
export function start(x: number): number {
  return x;
}
/**
 * @pre 0 <= x && x <= 10 && x <= n && n <= 100
 * @post result >= 0 && result <= 100
 */
export function f(n: number, x: number): number {
  let i = start(x);
  let acc = 0;
  /**
   * @invariant x <= i && i <= n && 0 <= acc && acc <= i
   * @decreases n - i
   */
  for (; i < n; i = i + 1) {
    acc = acc + 1;
  }
  return acc;
}
`;
    // `i` is an ordinary carried `let` here: extraction reports nothing (the invariant's
    // provability is the certification step's business).
    expect(fragmentErrors(source)).toEqual([]);
  });

  test("the loop variable of a `for` loop updated with `i++` is in scope as well", () => {
    const source = canonical.replace("i = i + 1", "i++");
    expect(extract(source).diagnostics).toEqual([]);
  });
});
