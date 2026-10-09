/**
 * JSDoc block parsing.
 *
 * A `/** … *\/` block is split into tags.  Continuation lines lose their leading
 * `*`, multi-line tags are joined with a single space, and the verbatim text of
 * each tag is kept.  This module deliberately does **not** parse expressions:
 * `parser.ts` does that on demand, using the tag text plus `tagSourceOffset` to
 * map expression offsets back into the file so diagnostics point at the source.
 *
 * Errors (all `parse`, located):
 *   - an empty tag (`@pre` with no expression);
 *   - an `@` inside a spec expression (it would start a new tag);
 *   - an unknown tag (`@foo`) in a block that also has spec tags.
 *
 * A block without spec tags is prose and never produces an error, so a plain
 * documentation comment on a function is harmless.
 */

import { type Diagnostic, type Span, sortDiagnostics } from "../diagnostics";

/** Tag names the verifier understands. */
export const SPEC_TAG_NAMES: ReadonlySet<string> = new Set(["pre", "post", "decreases", "invariant"]);

export type SpecTagName = "pre" | "post" | "decreases" | "invariant";

/**
 * A run of a tag's text that came from one source line.  `textOffset` is the
 * offset of the run inside `JSDocTag.text`; `sourceOffset` is its offset in the
 * file.  The one-character gap between two runs (the joining space) maps to the
 * end of the earlier run.
 */
export interface TagSegment {
  textOffset: number;
  sourceOffset: number;
  length: number;
}

export interface JSDocTag {
  /** Tag name without the `@`. */
  name: string;
  /** Joined tag text with continuation `*` markers stripped; `""` when empty. */
  text: string;
  /** Verbatim source text of the tag, from `@` to the end of its last line. */
  raw: string;
  /** Whole tag: from `@` to the end of the last text run. */
  span: Span;
  /** Just the `@name` part. */
  nameSpan: Span;
  /** The text part; a zero-length span at the name end when the tag is empty. */
  textSpan: Span;
  isSpec: boolean;
  segments: TagSegment[];
}

export interface JSDocBlock {
  raw: string;
  span: Span;
  tags: JSDocTag[];
  /** Lines outside any tag, joined with newlines (the prose description). */
  prose: string;
  diagnostics: Diagnostic[];
  hasSpecTags: boolean;
}

interface Line {
  /** Absolute offset of the line's first character. */
  start: number;
  /** Absolute offset just past the line's last character (excluding `\n`). */
  end: number;
  /** Content after stripping leading whitespace, a leading `*`, and one space. */
  content: string;
  /** Absolute offset of `content`'s first character. */
  contentStart: number;
}

interface TagBuilder {
  name: string;
  nameStart: number;
  nameEnd: number;
  text: string;
  segments: TagSegment[];
}

function isSpace(ch: string | undefined): boolean {
  return ch === " " || ch === "\t" || ch === "\r" || ch === "\v" || ch === "\f";
}

function splitLines(raw: string, base: number): Line[] {
  const lines: Line[] = [];
  let start = 0;
  for (let i = 0; i <= raw.length; i += 1) {
    if (i === raw.length || raw[i] === "\n") {
      let end = i;
      if (end > start && raw[end - 1] === "\r") end -= 1;
      lines.push({ start: base + start, end: base + end, content: "", contentStart: base + end });
      start = i + 1;
    }
  }
  // Strip the delimiters: `/**` on the first line, `*/` on the last.
  const first = lines[0]!;
  first.start += 3;
  const last = lines[lines.length - 1]!;
  last.end = Math.max(last.start, last.end - 2);
  for (const line of lines) {
    let i = line.start;
    const text = raw.slice(line.start - base, line.end - base);
    let j = 0;
    while (j < text.length && isSpace(text[j])) j += 1;
    if (text[j] === "*") {
      j += 1;
      if (isSpace(text[j])) j += 1;
    }
    let k = text.length;
    while (k > j && isSpace(text[k - 1])) k -= 1;
    line.content = text.slice(j, k);
    line.contentStart = line.start + j;
  }
  return lines;
}

function positionSpan(span: Span, raw: string, startRel: number, endRel: number): Span {
  // The lexer gave us the block's start position; recompute offsets inside it.
  let line = span.line;
  let col = span.col;
  for (let i = 0; i < startRel && i < raw.length; i += 1) {
    if (raw[i] === "\n") {
      line += 1;
      col = 1;
    } else {
      col += 1;
    }
  }
  return { file: span.file, line, col, offset: span.offset + startRel, endOffset: span.offset + endRel };
}

/** Parse one JSDoc block.  `raw` must be the exact `/** … *\/` text of `span`. */
export function parseJSDoc(raw: string, span: Span): JSDocBlock {
  const diagnostics: Diagnostic[] = [];
  const tags: JSDocTag[] = [];
  const proseLines: string[] = [];

  if (!raw.startsWith("/**") || !raw.endsWith("*/") || raw.length < 5) {
    diagnostics.push({
      kind: "parse",
      severity: "error",
      span,
      message: "malformed JSDoc block",
    });
    return { raw, span, tags, prose: "", diagnostics, hasSpecTags: false };
  }

  const lines = splitLines(raw, span.offset);
  let current: TagBuilder | null = null;

  const finishTag = (): void => {
    if (current === null) return;
    const builder = current;
    current = null;
    const isSpec = SPEC_TAG_NAMES.has(builder.name);
    const firstSegment = builder.segments[0];
    const lastSegment = builder.segments[builder.segments.length - 1];
    const nameStartRel = builder.nameStart - span.offset;
    const nameEndRel = builder.nameEnd - span.offset;
    const textStartRel = firstSegment === undefined ? nameEndRel : firstSegment.sourceOffset - span.offset;
    const textEndRel = lastSegment === undefined ? nameEndRel : lastSegment.sourceOffset + lastSegment.length - span.offset;
    const nameSpan = positionSpan(span, raw, nameStartRel, nameEndRel);
    const textSpan = positionSpan(span, raw, textStartRel, textEndRel);
    const tagSpan = positionSpan(span, raw, nameStartRel, textEndRel);
    const tag: JSDocTag = {
      name: builder.name,
      text: builder.text,
      raw: raw.slice(nameStartRel, textEndRel),
      span: tagSpan,
      nameSpan,
      textSpan,
      isSpec,
      segments: builder.segments,
    };
    if (tag.text.trim() === "") {
      diagnostics.push({
        kind: "parse",
        severity: "error",
        span: tag.span,
        message: `empty \`@${tag.name}\` tag: expected an expression`,
      });
    }
    tags.push(tag);
  };

  const appendTo = (builder: TagBuilder, chunk: string, chunkSourceStart: number): void => {
    let start = 0;
    while (start < chunk.length && isSpace(chunk[start])) start += 1;
    let end = chunk.length;
    while (end > start && isSpace(chunk[end - 1])) end -= 1;
    const trimmed = chunk.slice(start, end);
    if (trimmed === "") return;
    if (builder.text.length > 0) builder.text += " ";
    const textOffset = builder.text.length;
    builder.text += trimmed;
    builder.segments.push({
      textOffset,
      sourceOffset: chunkSourceStart + start,
      length: trimmed.length,
    });
    if (SPEC_TAG_NAMES.has(builder.name)) {
      const at = trimmed.indexOf("@");
      if (at !== -1) {
        const offset = chunkSourceStart + start + at;
        diagnostics.push({
          kind: "parse",
          severity: "error",
          span: positionSpan(span, raw, offset - span.offset, offset - span.offset + 1),
          message: "`@` is not allowed inside a spec expression; start each tag on its own line",
        });
      }
    }
  };

  for (const line of lines) {
    const content = line.content;
    if (content === "") continue;
    if (content.startsWith("@")) {
      const match = /^@([A-Za-z_$][A-Za-z0-9_$-]*)/.exec(content);
      if (match !== null) {
        finishTag();
        const nameStart = line.contentStart;
        const nameEnd = nameStart + match[0].length;
        current = { name: match[1]!, nameStart, nameEnd, text: "", segments: [] };
        appendTo(current, content.slice(match[0].length), nameEnd);
        continue;
      }
      if (current !== null) {
        const offset = line.contentStart;
        diagnostics.push({
          kind: "parse",
          severity: "error",
          span: positionSpan(span, raw, offset - span.offset, offset - span.offset + 1),
          message: "`@` is not allowed inside a spec expression; start each tag on its own line",
        });
      } else {
        proseLines.push(content);
      }
      continue;
    }
    if (current !== null) {
      appendTo(current, content, line.contentStart);
    } else {
      proseLines.push(content);
    }
  }
  finishTag();

  const hasSpecTags = tags.some((tag) => tag.isSpec);
  if (hasSpecTags) {
    for (const tag of tags) {
      if (!tag.isSpec) {
        diagnostics.push({
          kind: "parse",
          severity: "error",
          span: tag.nameSpan,
          message: `unknown JSDoc tag \`@${tag.name}\` next to spec tags`,
        });
      }
    }
  }

  return {
    raw,
    span,
    tags,
    prose: proseLines.join("\n"),
    diagnostics: sortDiagnostics(diagnostics),
    hasSpecTags,
  };
}

/** Spec tags (`@pre`, `@post`, `@decreases`, `@invariant`) in source order. */
export function specTags(block: JSDocBlock): JSDocTag[] {
  return block.tags.filter((tag) => tag.isSpec);
}

/** Tags with the given name, in source order. */
export function tagsNamed(block: JSDocBlock, name: SpecTagName): JSDocTag[] {
  return block.tags.filter((tag) => tag.name === name);
}

/**
 * Map an offset inside `tag.text` back to an offset in the source file.  The
 * joining space between two lines maps to the end of the earlier line.
 */
export function tagSourceOffset(tag: JSDocTag, textOffset: number): number {
  if (tag.segments.length === 0) return tag.nameSpan.offset;
  for (const segment of tag.segments) {
    if (textOffset <= segment.textOffset + segment.length) {
      return segment.sourceOffset + Math.max(0, textOffset - segment.textOffset);
    }
  }
  const last = tag.segments[tag.segments.length - 1]!;
  return last.sourceOffset + last.length;
}
