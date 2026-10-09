/**
 * Shared diagnostic vocabulary, used by every later milestone.
 *
 * A `Span` is a located range of a source file.  Lines and columns are 1-based,
 * offsets are 0-based indices into the source string (UTF-16 code units, exactly
 * like `String.prototype.slice`).  `endOffset` is exclusive and optional so that
 * callers that only know a point can still build a span.
 *
 * `formatDiagnostic` renders the section 4.3 shape:
 *
 *   examples/fail/clampNoPre.ts:6:3: error[post]: postcondition `lo <= result && result <= hi` may not hold
 *     path: x >= lo, x > hi
 *     counterexample: x = 1, lo = 1, hi = 0
 */

export interface Span {
  file: string;
  /** 1-based line. */
  line: number;
  /** 1-based column. */
  col: number;
  /** 0-based offset of the first character. */
  offset: number;
  /** 0-based exclusive end offset; defaults to `offset` when absent. */
  endOffset?: number;
}

export type DiagnosticKind =
  | "pre-call"
  | "post"
  | "index"
  | "slice"
  | "append-length"
  | "range"
  | "measure-nonneg"
  | "measure-decrease"
  | "invariant-init"
  | "invariant-preserve"
  | "fragment"
  | "parse"
  | "uncertified"
  | "internal";

export type DiagnosticSeverity = "error" | "warning";

export interface Diagnostic {
  kind: DiagnosticKind;
  severity: DiagnosticSeverity;
  span: Span;
  message: string;
  /** Case path that produced the diagnostic, filled in by later milestones. */
  path?: string[];
  /** Variable name -> printed value, filled in by later milestones. */
  counterexample?: Record<string, string>;
}

/** Render one diagnostic exactly as section 4.3 shows it. */
export function formatDiagnostic(d: Diagnostic): string {
  const lines = [`${d.span.file}:${d.span.line}:${d.span.col}: ${d.severity}[${d.kind}]: ${d.message}`];
  if (d.path !== undefined && d.path.length > 0) {
    lines.push(`  path: ${d.path.join(", ")}`);
  }
  if (d.counterexample !== undefined) {
    const entries = Object.entries(d.counterexample);
    if (entries.length > 0) {
      lines.push(`  counterexample: ${entries.map(([name, value]) => `${name} = ${value}`).join(", ")}`);
    }
  }
  return lines.join("\n");
}

export function formatDiagnostics(diagnostics: readonly Diagnostic[]): string {
  return diagnostics.map(formatDiagnostic).join("\n");
}

/** Deterministic source order: file, then offset, then end, then message. */
export function compareDiagnostics(a: Diagnostic, b: Diagnostic): number {
  if (a.span.file !== b.span.file) return a.span.file < b.span.file ? -1 : 1;
  if (a.span.offset !== b.span.offset) return a.span.offset - b.span.offset;
  const ae = a.span.endOffset ?? a.span.offset;
  const be = b.span.endOffset ?? b.span.offset;
  if (ae !== be) return ae - be;
  if (a.kind !== b.kind) return a.kind < b.kind ? -1 : 1;
  if (a.message === b.message) return 0;
  return a.message < b.message ? -1 : 1;
}

export function sortDiagnostics<T extends Diagnostic>(diagnostics: readonly T[]): T[] {
  return [...diagnostics].sort(compareDiagnostics);
}

export function hasErrors(diagnostics: readonly Diagnostic[]): boolean {
  return diagnostics.some((d) => d.severity === "error");
}

/** Offsets at which each line starts; `lineStarts(source).length` is the line count. */
export function lineStarts(source: string): number[] {
  const starts = [0];
  for (let i = 0; i < source.length; i += 1) {
    if (source[i] === "\n") starts.push(i + 1);
  }
  return starts;
}

export interface Position {
  line: number;
  col: number;
}

/** 1-based line/column of a 0-based offset. */
export function offsetToPosition(source: string, offset: number, starts?: readonly number[]): Position {
  const table = starts ?? lineStarts(source);
  const clamped = Math.max(0, Math.min(offset, source.length));
  let lo = 0;
  let hi = table.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (table[mid]! <= clamped) lo = mid;
    else hi = mid - 1;
  }
  return { line: lo + 1, col: clamped - table[lo]! + 1 };
}

/** Build a span from offsets, computing line/column. */
export function spanFromOffsets(file: string, source: string, start: number, end?: number): Span {
  const { line, col } = offsetToPosition(source, start);
  return { file, line, col, offset: start, endOffset: end ?? start };
}

/** A span covering `first` through the end of `last`; both must be in the same file. */
export function joinSpans(first: Span, last: Span): Span {
  const end = last.endOffset ?? last.offset;
  return {
    file: first.file,
    line: first.line,
    col: first.col,
    offset: first.offset,
    endOffset: Math.max(end, first.offset),
  };
}

/** The source text a span covers. */
export function spanText(source: string, span: Span): string {
  return source.slice(span.offset, span.endOffset ?? span.offset);
}

export function spanLength(span: Span): number {
  return (span.endOffset ?? span.offset) - span.offset;
}

/** True when `inner` lies inside `outer` (same file, by offsets). */
export function spanContains(outer: Span, inner: Span): boolean {
  if (outer.file !== inner.file) return false;
  return inner.offset >= outer.offset && (inner.endOffset ?? inner.offset) <= (outer.endOffset ?? outer.offset);
}
