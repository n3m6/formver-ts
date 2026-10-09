/**
 * Spec-expression parse errors must point at the token the parser gave up on, not at the
 * first character of the JSDoc tag: a multi-line `@pre` that is wrong on its second line
 * should report that line (section 4.3 asks for a `file:line:col` diagnostic).
 */
import { describe, expect, test } from "bun:test";
import { verify } from "../../src/verify";

const cases: ReadonlyArray<{ name: string; source: string; line: number; message: string }> = [
  {
    name: "a multi-line tag points at the failing continuation line",
    source: `/**
 * @pre lo <= hi &&
 *      hi <=
 */
export function f(lo: number, hi: number): number {
  return lo;
}
`,
    line: 3,
    message: "cannot parse this spec expression",
  },
  {
    name: "trailing junk points at the junk token",
    source: `/**
 * @pre lo <= hi zzz
 */
export function f(lo: number, hi: number): number {
  return lo;
}
`,
    line: 2,
    message: "cannot parse this spec expression",
  },
];

describe("spec-expression error locations", () => {
  for (const { name, source, line, message } of cases) {
    test(name, () => {
      const result = verify("/tmp/specspans.ts", source, { strict: false });
      const diagnostic = result.diagnostics.find((d) => d.kind === "parse");
      expect(diagnostic).toBeDefined();
      expect(diagnostic!.message).toContain(message);
      expect(diagnostic!.span.line).toBe(line);
      expect(diagnostic!.span.col).toBeGreaterThan(1);
      // The function is rejected, never certified.
      expect(result.functions.every((fn) => fn.status !== "certified")).toBe(true);
    });
  }
});
