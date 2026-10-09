/**
 * Cross-check: compare our parse against Bun's own printer (section 6.2).
 *
 * Bun exposes no syntax tree, but its printer drops redundant parentheses and
 * re-indents, so two texts normalise to the same output exactly when they parse
 * to the same tree.  We print our AST with every subexpression parenthesised
 * (`print.ts`) and compare.  A mismatch is an `internal` diagnostic: either our
 * parser is wrong or the original is not valid TypeScript.
 *
 *   const bun = new Bun.Transpiler({ loader: "ts" });
 *   const norm = (code: string) => bun.transformSync(code).trim();
 *   export function sameParse(originalText, ourParenthesizedText) {
 *     return norm(originalText) === norm(ourParenthesizedText);
 *   }
 *
 * `Bun.Transpiler` normalises type aliases to the empty string, so only
 * functions can be cross-checked.
 */

import type { Diagnostic } from "../diagnostics";
import type { FnDecl } from "./ast";
import { printFunction } from "./print";

const bun = new Bun.Transpiler({ loader: "ts" });

/** Bun's normal form of a snippet.  Throws when Bun cannot parse the snippet. */
export function normalizeWithBun(code: string): string {
  return bun.transformSync(code).trim();
}

export function sameParse(originalText: string, ourParenthesizedText: string): boolean {
  return normalizeWithBun(originalText) === normalizeWithBun(ourParenthesizedText);
}

/** First differing line pair, for a short, useful message. */
function firstDifference(a: string, b: string): string {
  const left = a.split("\n");
  const right = b.split("\n");
  const count = Math.max(left.length, right.length);
  for (let i = 0; i < count; i += 1) {
    if (left[i] !== right[i]) {
      return `line ${i + 1}: original ${JSON.stringify(left[i] ?? "<end>")} vs printout ${JSON.stringify(right[i] ?? "<end>")}`;
    }
  }
  return "";
}

/**
 * Cross-check one parsed function.  Returns an `internal` diagnostic on
 * mismatch, or `null` when Bun normalises the original and our printout
 * identically.
 */
export function crosscheckFunction(fn: FnDecl, source: string): Diagnostic | null {
  const original =
    fn.text !== ""
      ? fn.text
      : source.slice(fn.span.offset, fn.span.endOffset ?? fn.span.offset);
  let printed: string;
  try {
    printed = printFunction(fn);
  } catch (error) {
    return {
      kind: "internal",
      severity: "error",
      span: fn.span,
      message: `cross-check failed for \`${fn.name}\`: our printer threw ${
        error instanceof Error ? error.message : String(error)
      }`,
    };
  }
  let originalNormal: string;
  let printedNormal: string;
  try {
    originalNormal = normalizeWithBun(original);
    printedNormal = normalizeWithBun(printed);
  } catch (error) {
    return {
      kind: "internal",
      severity: "error",
      span: fn.span,
      message: `cross-check failed for \`${fn.name}\`: Bun could not transform ${
        error instanceof Error ? `(${error.message})` : ""
      }`.trimEnd(),
    };
  }
  if (originalNormal === printedNormal) return null;
  return {
    kind: "internal",
    severity: "error",
    span: fn.span,
    message: `cross-check failed for \`${fn.name}\`: our parse does not match Bun's (${firstDifference(
      originalNormal,
      printedNormal,
    )})`,
  };
}

/** Cross-check every function in a parsed file. */
export function crosscheckFunctions(functions: readonly FnDecl[], source: string): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  for (const fn of functions) {
    const diagnostic = crosscheckFunction(fn, source);
    if (diagnostic !== null) diagnostics.push(diagnostic);
  }
  return diagnostics;
}
