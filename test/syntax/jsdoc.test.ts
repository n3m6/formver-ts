/**
 * JSDoc tests (section 9.2): multi-line tags, empty tags, `@` inside an
 * expression, braces kept as written, unknown tags, and the text→source offset
 * mapping the spec parser will need.
 */
import { describe, expect, test } from "bun:test";
import { offsetToPosition } from "../../src/diagnostics";
import { parseJSDoc, tagSourceOffset } from "../../src/syntax/jsdoc";
import { lex } from "../../src/syntax/lexer";

/** Parse the first JSDoc block of a file, with spans computed from the source. */
function doc(source: string) {
  const tokens = lex(source, "t.ts").tokens;
  const token = tokens.find((t) => t.kind === "jsdoc");
  if (token === undefined) throw new Error("no JSDoc block in the source");
  return { block: parseJSDoc(token.text, token.span), token, source };
}

describe("tags", () => {
  test("multi-line tags are joined with a single space and keep their raw text", () => {
    const { block } = doc(`/**
 * Prose description.
 * @pre lo <= hi &&
 *      hi <= 100
 * @post result <= hi
 */`);
    expect(block.prose).toBe("Prose description.");
    expect(block.tags.map((t) => t.name)).toEqual(["pre", "post"]);
    const pre = block.tags[0]!;
    expect(pre.text).toBe("lo <= hi && hi <= 100");
    expect(pre.raw).toContain("@pre lo <= hi &&");
    expect(pre.isSpec).toBe(true);
    expect(block.hasSpecTags).toBe(true);
    expect(block.diagnostics).toEqual([]);
  });

  test("a tag with no expression is an error at the tag", () => {
    const { block } = doc(`/**
 * @pre
 * @post result >= 0
 */`);
    expect(block.diagnostics.length).toBe(1);
    expect(block.diagnostics[0]!.message).toContain("empty `@pre` tag");
    expect(block.diagnostics[0]!.span.line).toBe(2);
    expect(block.diagnostics[0]!.span.col).toBe(4);
  });

  test("an empty tag at the end of a block is an error too", () => {
    const { block } = doc("/** @post result >= 0\n * @pre */");
    expect(block.diagnostics.map((d) => d.message)).toEqual([
      "empty `@pre` tag: expected an expression",
    ]);
  });

  test("`@` inside a spec expression is an error", () => {
    const { block } = doc(`/**
 * @pre x > 0 @ y
 */`);
    expect(block.diagnostics.length).toBe(1);
    expect(block.diagnostics[0]!.message).toContain("`@` is not allowed inside a spec expression");
    // The error points at the `@` on line 2 (after `@pre x > 0 `).
    expect(block.diagnostics[0]!.span).toMatchObject({ line: 2, col: 15 });
  });

  test("an `@` inside a non-spec tag or in prose is not an error", () => {
    expect(doc("/** mail me @example.com */").block.diagnostics).toEqual([]);
    expect(doc("/**\n * @author someone@example.com\n */").block.diagnostics).toEqual([]);
  });

  test("braces are kept exactly as written", () => {
    const { block } = doc(`/**
 * @pre f({ a: 1 }, b[0]) && (x > 0)
 * @post result === { ok: true }.ok ? 1 : 0
 */`);
    expect(block.tags[0]!.text).toBe("f({ a: 1 }, b[0]) && (x > 0)");
    expect(block.tags[1]!.text).toBe("result === { ok: true }.ok ? 1 : 0");
    expect(block.diagnostics).toEqual([]);
  });

  test("an unknown tag next to spec tags is an error; a prose-only block is not", () => {
    const withSpec = doc(`/**
 * @pre x > 0
 * @foo bar
 */`).block;
    expect(withSpec.diagnostics.map((d) => d.message)).toEqual([
      "unknown JSDoc tag `@foo` next to spec tags",
    ]);
    const proseOnly = doc(`/**
 * @param x the input
 * @returns the output
 */`).block;
    expect(proseOnly.diagnostics).toEqual([]);
    expect(proseOnly.hasSpecTags).toBe(false);
    expect(proseOnly.tags.map((t) => t.name)).toEqual(["param", "returns"]);
  });

  test("`@invariant` and `@decreases` are known spec tags", () => {
    const { block } = doc(`/**
 * @invariant 0 <= i && i <= n
 * @decreases n - i
 */`);
    expect(block.hasSpecTags).toBe(true);
    expect(block.diagnostics).toEqual([]);
  });

  test("a malformed block is reported rather than throwing", () => {
    const bad = parseJSDoc("/* not jsdoc */", {
      file: "t.ts",
      line: 1,
      col: 1,
      offset: 0,
      endOffset: 15,
    });
    expect(bad.diagnostics.map((d) => d.message)).toEqual(["malformed JSDoc block"]);
  });
});

describe("text offsets map back to the file", () => {
  test("each segment maps, and the joining space maps to the end of the previous line", () => {
    const source = `/**
 * @pre lo <= hi &&
 *      hi <= 100
 */
function f() {}`;
    const { block, source: text } = doc(source);
    const pre = block.tags[0]!;
    expect(pre.text).toBe("lo <= hi && hi <= 100");
    // `lo` is at text offset 0 -> source offset of the `l` on line 2.
    expect(offsetToPosition(text, tagSourceOffset(pre, 0))).toEqual({ line: 2, col: 9 });
    // `hi <= 100` starts on line 3.
    expect(offsetToPosition(text, tagSourceOffset(pre, pre.text.indexOf("hi <= 100")))).toEqual({
      line: 3,
      col: 9,
    });
    // An offset inside the joining space clamps to the end of the first line.
    const first = pre.segments[0]!;
    const joinOffset = tagSourceOffset(pre, first.textOffset + first.length);
    expect(joinOffset).toBe(first.sourceOffset + first.length);
    expect(pre.segments[1]!.textOffset).toBe(first.textOffset + first.length + 1);
  });

  test("the tag span covers `@name` through the last text character", () => {
    const { block } = doc(`/**
 * @pre x > 0
 */`);
    const pre = block.tags[0]!;
    expect(pre.nameSpan).toMatchObject({ line: 2, col: 4 });
    expect(pre.textSpan).toMatchObject({ line: 2, col: 9 });
    expect(pre.span.offset).toBe(pre.nameSpan.offset);
    expect(pre.span.endOffset).toBe(pre.textSpan.endOffset);
    expect(pre.textSpan.endOffset! - pre.textSpan.offset).toBe("x > 0".length);
  });
});
