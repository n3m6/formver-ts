/**
 * Same-line runtime-check injection (specification 6.6, milestone 8).
 *
 * `inject(source, plan, options)` takes one file's source and the `plan[]` `verify()` produced
 * for it and returns the source with runtime checks inserted **inside the existing lines**:
 * no newline is ever inserted, so stack-trace line numbers stay exact (only columns shift,
 * section 3.1 point 8).  Nothing is ever deleted either: an injection is a set of text
 * insertions, which makes "the original source is a subsequence of the output" a property a
 * test can assert directly.
 *
 * The plan says *what* to check and *where*; the source is parsed again here to find the
 * constructs the plan points at (an `a[i]`, a `return`, a loop).  Insertions are anchored to
 * the original offsets and applied as one nested edit tree, so wrapping an expression that
 * also contains a wrapped sub-expression (`a[i + 1]`, a `return` of a ternary) nests
 * correctly.  When an edit cannot be placed — the plan points at something the parser does
 * not see, a span does not correspond to a complete expression — injection **fails loudly**
 * with a located `internal` diagnostic instead of producing code that no longer parses.
 *
 * Verification never runs user code; injection edits text only.
 */
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { formatDiagnostic, type Diagnostic, type Span } from "../diagnostics";
import { resolveImportPath } from "../extract/specs";
import { tagsNamed, type JSDocTag } from "../syntax/jsdoc";
import { lex, type Token } from "../syntax/lexer";
import { parseFile } from "../syntax/parser";
import type * as A from "../syntax/ast";
import type { InjectionRecord } from "../verify";

/** The runtime module every injected file imports (`src/inject/runtime.ts`). */
export const RUNTIME_MODULE_PATH: string = resolve(import.meta.dir, "runtime.ts");

/** Thrown when a required edit is impossible; `diagnostic` locates the failure. */
export class InjectionError extends Error {
  readonly diagnostic: Diagnostic;

  constructor(diagnostic: Diagnostic) {
    super(formatDiagnostic(diagnostic));
    this.name = "InjectionError";
    this.diagnostic = diagnostic;
  }
}

export interface InjectOptions {
  /** Production: drop certified postconditions and certified internal checks. */
  readonly production?: boolean;
  /** The file path used for locations; defaults to the plan's first span's file. */
  readonly path?: string;
  /** Overrides the runtime module path the injected import points at. */
  readonly runtimePath?: string;
  /** An existing parse of the source (the caller often has one). */
  readonly parsed?: A.ParsedFile;
  /** Reads imported files to find a callee's `@pre`/`@decreases` spec; defaults to `node:fs`. */
  readonly readFile?: (path: string) => string;
}

// ---------------------------------------------------------------------------
// Edits
// ---------------------------------------------------------------------------

/**
 * One insertion.  `start === end` is a point insertion (`prefix` only): the text that is
 * already there stays where it is.  `start < end` is a **wrap**: `prefix` goes before the
 * region and `suffix` after it, so `f(e)` becomes `prefix + e + suffix`.
 */
interface Edit {
  readonly start: number;
  readonly end: number;
  readonly prefix: string;
  readonly suffix: string;
  readonly order: number;
}

interface EditNode {
  readonly edit: Edit;
  readonly children: EditNode[];
}

/**
 * Apply the edits as a nested tree.  Edits are sorted outer-first (a longer region at the
 * same offset is the outer one) and a point insertion sorts before a wrap that starts at the
 * same offset, so `a[i + 1]` becomes `a[__dv.checkIndex(a, __dv.checkRange(i + 1, "…"), "…")]`
 * — every check receives the value the inner checks produced.
 */
function applyEdits(source: string, edits: readonly Edit[], fail: (message: string) => never): string {
  const sorted = [...edits].sort(compareEdits);
  const roots: EditNode[] = [];
  const stack: EditNode[] = [];
  for (const edit of sorted) {
    while (stack.length > 0 && !containsEdit(stack[stack.length - 1]!.edit, edit)) stack.pop();
    const node: EditNode = { edit, children: [] };
    if (stack.length === 0) roots.push(node);
    else stack[stack.length - 1]!.children.push(node);
    stack.push(node);
  }
  const emit = (node: EditNode): string => {
    let out = node.edit.prefix;
    let cursor = node.edit.start;
    for (const child of node.children) {
      if (child.edit.start < cursor) fail("two injections overlap partially; cannot place them both");
      out += source.slice(cursor, child.edit.start) + emit(child);
      cursor = child.edit.end;
    }
    out += source.slice(cursor, node.edit.end) + node.edit.suffix;
    return out;
  };
  let out = "";
  let cursor = 0;
  for (const root of roots) {
    if (root.edit.start < cursor) fail("two injections overlap partially; cannot place them both");
    out += source.slice(cursor, root.edit.start) + emit(root);
    cursor = root.edit.end;
  }
  return out + source.slice(cursor);
}

/** Points first, then wrappers (longest region first), then insertion order. */
function compareEdits(a: Edit, b: Edit): number {
  if (a.start !== b.start) return a.start - b.start;
  const aPoint = a.start === a.end ? 1 : 0;
  const bPoint = b.start === b.end ? 1 : 0;
  if (aPoint !== bPoint) return bPoint - aPoint;
  if (a.end !== b.end) return b.end - a.end;
  return a.order - b.order;
}

function containsEdit(parent: Edit, child: Edit): boolean {
  return child.start >= parent.start && child.end <= parent.end;
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

interface Context {
  readonly source: string;
  readonly tokens: readonly Token[];
  readonly path: string;
  readonly parsed: A.ParsedFile;
  readonly options: InjectOptions;
  readonly edits: Edit[];
  readonly productions: boolean;
  /** Function names called from code that is not a verified function (production rule). */
  readonly unverifiedCallers: ReadonlySet<string>;
  /** Imported files, parsed once, for their callees' `@pre`/`@decreases` tags. */
  readonly calleeCache: Map<string, A.ParsedFile | null>;
  order: number;
  /** The first record that asked for an edit, for a located failure message. */
  current?: InjectionRecord;
}

export function inject(source: string, plan: readonly InjectionRecord[], options: InjectOptions = {}): string {
  if (plan.length === 0) return source;
  const path = options.path ?? plan[0]!.span.file;
  const runtimePath = options.runtimePath ?? RUNTIME_MODULE_PATH;
  const importText = `import * as __dv from ${JSON.stringify(runtimePath)};`;
  // Idempotent: a file that already imports the runtime module has been injected.
  if (source.includes(importText)) return source;
  const parsed = options.parsed ?? parseFile(path, source, { includeUnannotated: true });
  const tokens = lex(source, path).tokens;
  const context: Context = {
    source,
    tokens,
    path,
    parsed,
    options,
    edits: [],
    productions: options.production === true,
    unverifiedCallers: calledFromUnverifiedCode(parsed, tokens),
    calleeCache: new Map(),
    order: 0,
  };
  context.edits.push(point(importOffset(source), importText, context));
  const groups = new Map<string, InjectionRecord[]>();
  for (const record of plan) {
    const list = groups.get(record.function);
    if (list === undefined) groups.set(record.function, [record]);
    else list.push(record);
  }
  for (const [name, records] of groups) injectFunction(context, name, records);
  const output = applyEdits(source, context.edits, (message) => fail(context, message));
  validateOutput(context, output);
  return output;
}

function fail(context: Context, message: string, span?: Span): never {
  const at = span ?? context.current?.span ?? { file: context.path, line: 1, col: 1, offset: 0 };
  throw new InjectionError({ kind: "internal", severity: "error", span: at, message });
}

function point(offset: number, text: string, context: Context): Edit {
  context.order += 1;
  return { start: offset, end: offset, prefix: text, suffix: "", order: context.order };
}

function wrap(start: number, end: number, prefix: string, suffix: string, context: Context): Edit {
  context.order += 1;
  return { start, end, prefix, suffix, order: context.order };
}

/** Where the runtime import goes: line 1, or line 2 after a `#!` shebang. */
function importOffset(source: string): number {
  if (!source.startsWith("#!")) return 0;
  const newline = source.indexOf("\n");
  return newline === -1 ? source.length : newline + 1;
}

/** The final safety net: the injected file must still parse as TypeScript. */
function validateOutput(context: Context, output: string): void {
  try {
    new Bun.Transpiler({ loader: "ts" }).transformSync(output);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    fail(context, `injection made ${context.path} unparseable, so nothing was injected: ${message}`);
  }
}

// ---------------------------------------------------------------------------
// Which records stay
// ---------------------------------------------------------------------------

function injectFunction(context: Context, name: string, records: readonly InjectionRecord[]): void {
  const first = records[0]!;
  const decl = declarationOf(context, name, first);
  const kept = records.filter((record) => keepRecord(context, record));
  if (kept.length === 0) return;
  const index = buildIndex(decl.body);
  injectEntry(context, decl, kept);
  injectReturns(context, decl, index, kept);
  injectLoops(context, decl, index, kept);
  for (const record of kept) {
    switch (record.kind) {
      case "index":
      case "slice":
      case "append-length":
      case "range":
      case "pre-call":
      case "measure-nonneg":
      case "measure-decrease":
        injectInternal(context, decl, index, record);
        break;
      default:
        break;
    }
  }
}

function declarationOf(context: Context, name: string, record: InjectionRecord): A.FnDecl {
  const decl = context.parsed.functions.find((fn) => fn.name === name);
  if (decl === undefined) {
    fail(context, `the injection plan mentions \`${name}\`, but ${context.path} has no such function declaration`, record.span);
  }
  return decl;
}

/**
 * The production stripping table (specification 6.6):
 *
 * | record                                        | development | production |
 * |-----------------------------------------------|-------------|------------|
 * | boundary guard of an exported parameter       | keep        | keep       |
 * | `@pre` of an exported function                | keep        | keep       |
 * | `@pre` of a non-exported function called from unverified code | keep | keep |
 * | `@pre` of a non-exported function, all callers verified       | keep | drop |
 * | `@post` (certified)                           | keep        | drop       |
 * | `@post` (uncertified)                         | keep        | keep       |
 * | internal obligation (certified)               | keep        | drop       |
 * | internal obligation (uncertified)             | keep        | keep       |
 */
function keepRecord(context: Context, record: InjectionRecord): boolean {
  if (record.isBoundaryGuard) return true;
  if (record.kind === "pre" && record.isPrecondition) {
    if (!context.productions) return true;
    return record.exported || context.unverifiedCallers.has(record.function);
  }
  return !context.productions || !record.certified;
}

/** Names called from outside every verified function: the "unverified code in this file". */
function calledFromUnverifiedCode(parsed: A.ParsedFile, tokens: readonly Token[]): Set<string> {
  const verified = parsed.functions.filter((fn) => fn.jsdoc !== null && fn.jsdoc.hasSpecTags);
  const spans = verified.map((fn) => fn.span);
  const out = new Set<string>();
  for (let i = 0; i < tokens.length; i += 1) {
    const token = tokens[i]!;
    if (token.kind !== "ident") continue;
    const next = nextSignificant(tokens, i);
    if (next === undefined || next.kind !== "punct" || next.text !== "(") continue;
    // A declaration (`function f(…`, `class C(…)`) is not a call.
    const previous = previousSignificant(tokens, i);
    if (previous !== undefined && (previous.text === "function" || previous.text === "class")) continue;
    const inside = spans.some(
      (span) => token.span.offset >= span.offset && token.span.offset < (span.endOffset ?? span.offset),
    );
    if (!inside) out.add(token.text);
  }
  return out;
}

function previousSignificant(tokens: readonly Token[], index: number): Token | undefined {
  for (let i = index - 1; i >= 0; i -= 1) {
    const token = tokens[i]!;
    if (token.kind === "jsdoc" || token.kind === "eof") continue;
    return token;
  }
  return undefined;
}

function nextSignificant(tokens: readonly Token[], index: number): Token | undefined {
  for (let i = index + 1; i < tokens.length; i += 1) {
    const token = tokens[i]!;
    if (token.kind === "jsdoc" || token.kind === "eof") continue;
    return token;
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// Entry: guards, then `@pre`
// ---------------------------------------------------------------------------

function injectEntry(context: Context, decl: A.FnDecl, kept: readonly InjectionRecord[]): void {
  const parts: string[] = [];
  for (const record of kept) {
    if (record.isBoundaryGuard) parts.push(guardCall(context, decl, record));
  }
  for (const record of kept) {
    if (record.kind !== "pre") continue;
    const text = requireSpecText(context, record);
    parts.push(
      `if (!(${text})) throw new __dv.PreconditionError(${quote(record.function)}, ${quote(text)}, ` +
        `{${parameterSnapshot(decl)}}, ${quote(location(record.span))});`,
    );
  }
  if (parts.length === 0) return;
  const open = decl.body.span.offset;
  if (context.source[open] !== "{") {
    fail(context, `the body of \`${decl.name}\` does not start with \`{\` where the plan expects it`, decl.body.span);
  }
  context.edits.push(point(open + 1, ` ${parts.join(" ")} `, context));
}

function parameterSnapshot(decl: A.FnDecl): string {
  return decl.params.map((param) => param.name).join(", ");
}

/** The boundary guard an exported parameter needs, from its declared type. */
function guardCall(context: Context, decl: A.FnDecl, record: InjectionRecord): string {
  const param = decl.params.find((candidate) => candidate.name === record.param);
  if (param === undefined) {
    fail(context, `the guard record names \`${record.param}\`, which \`${decl.name}\` does not declare`, record.span);
  }
  const args = `${quote(record.function)}, ${quote(param.name)}, ${param.name}`;
  switch (param.typeAnn?.kind) {
    case "NumberType":
      return `__dv.guardInt(${args});`;
    case "ArrayType":
      return param.typeAnn.elem.kind === "NumberType"
        ? `__dv.guardIntArray(${args});`
        : `__dv.guardArray(${args});`;
    case "NameType":
      return `__dv.guardUnion(${args});`;
    default:
      fail(
        context,
        `no boundary guard is defined for the type of \`${decl.name}\`'s parameter \`${param.name}\` ` +
          `(${param.typeText ?? param.typeAnn?.kind ?? "unannotated"}); this function is outside the fragment`,
        record.span,
      );
  }
}

// ---------------------------------------------------------------------------
// Returns: `@post`
// ---------------------------------------------------------------------------

function injectReturns(
  context: Context,
  decl: A.FnDecl,
  index: FunctionIndex,
  kept: readonly InjectionRecord[],
): void {
  const posts = kept.filter((record) => record.kind === "post");
  if (posts.length === 0) return;
  const snapshot = `${parameterSnapshot(decl)}${decl.params.length > 0 ? ", " : ""}result`;
  let checks = "";
  for (const record of posts) {
    const text = requireSpecText(context, record);
    checks +=
      `if (!(${text})) throw new __dv.PostconditionError(${quote(record.function)}, ${quote(text)}, ` +
      `{${snapshot}}, ${quote(location(record.span))}); `;
  }
  for (const statement of index.returns) {
    context.current = posts[0];
    if (statement.argument === null) {
      fail(context, `a bare \`return;\` cannot carry a postcondition check`, statement.span);
    }
    const extent = extentOrFail(context, statement.argument.span, "return value");
    context.edits.push(wrap(extent.start, extent.end, `((result) => { ${checks}return result; })(`, ")", context));
  }
}

// ---------------------------------------------------------------------------
// Loops: invariant and measure checks at the loop head
// ---------------------------------------------------------------------------

function injectLoops(context: Context, decl: A.FnDecl, index: FunctionIndex, kept: readonly InjectionRecord[]): void {
  const byLoop = new Map<number, InjectionRecord[]>();
  for (const record of kept) {
    if (!isLoopKind(record.kind)) continue;
    const loop = index.loopAt.get(record.span.offset);
    if (loop === undefined) continue; // a recursive-call measure site; handled below
    const list = byLoop.get(record.span.offset);
    if (list === undefined) byLoop.set(record.span.offset, [record]);
    else list.push(record);
  }
  for (const [offset, records] of byLoop) {
    const loop = index.loopAt.get(offset)!;
    context.current = records[0];
    const tags = loop.jsdoc;
    const invariants = tags === null ? [] : tagsNamed(tags, "invariant").map((tag) => tag.text);
    const decreases = tags === null ? [] : tagsNamed(tags, "decreases").map((tag) => tag.text);
    const kinds = new Set(records.map((record) => record.kind));
    const parts: string[] = [];
    const loc = location(records[0]!.span);
    if (kinds.has("invariant-init") || kinds.has("invariant-preserve")) {
      if (invariants.length === 0) fail(context, "the loop has an invariant obligation but no `@invariant` tag", loop.span);
      const text = invariants.map((one) => `(${one})`).join(" && ");
      parts.push(`__dv.checkInvariant(${text}, ${quote(decl.name)}, ${quote(text)}, ${quote(loc)});`);
    }
    if (kinds.has("measure-nonneg") || kinds.has("measure-decrease")) {
      if (decreases.length === 0) fail(context, "the loop has a measure obligation but no `@decreases` tag", loop.span);
      const text = decreases[0]!;
      parts.push(`__dv.checkMeasure(${text}, ${quote(decl.name)}, ${quote(`@decreases ${text}`)}, ${quote(loc)});`);
      // The strict-decrease monitor keeps state per source location, so it is only sound when
      // the loop cannot be re-entered while it is running: a loop of a non-recursive function.
      if (kinds.has("measure-decrease") && !isRecursive(decl, index)) {
        parts.push(
          `__dv.checkMeasureDecrease(${text}, ${quote(decl.name)}, ${quote(`@decreases ${text}`)}, ${quote(loc)});`,
        );
      }
    }
    if (parts.length === 0) continue;
    const body = loop.body;
    if (body.kind !== "Block") {
      fail(context, "a loop with an injected invariant must have a braced body", loop.span);
    }
    const open = body.span.offset;
    if (context.source[open] !== "{") fail(context, "the loop body does not start with `{`", body.span);
    context.edits.push(point(open + 1, ` ${parts.join(" ")} `, context));
  }
}

function isLoopKind(kind: InjectionRecord["kind"]): boolean {
  return (
    kind === "invariant-init" || kind === "invariant-preserve" || kind === "measure-nonneg" || kind === "measure-decrease"
  );
}

function isRecursive(decl: A.FnDecl, index: FunctionIndex): boolean {
  return index.expressions.some(
    (expression) =>
      expression.kind === "Call" &&
      expression.callee.kind === "Ident" &&
      expression.callee.name === decl.name,
  );
}

// ---------------------------------------------------------------------------
// Internal obligations: wrapped in place
// ---------------------------------------------------------------------------

function injectInternal(
  context: Context,
  decl: A.FnDecl,
  index: FunctionIndex,
  record: InjectionRecord,
): void {
  context.current = record;
  const loc = location(record.span);
  // A loop's invariant/measure records are injected once, at the loop head.
  if (isLoopKind(record.kind)) {
    if (index.loopAt.has(record.span.offset)) return;
    if (record.kind === "invariant-init" || record.kind === "invariant-preserve") {
      fail(context, "the plan points at a loop invariant, but there is no loop at that location", record.span);
    }
    // A `measure-*` record that is not a loop is a recursive call; fall through.
  }
  switch (record.kind) {
    case "index": {
      expressionAt(context, index, record, (expression) => expression.kind === "Index");
      const extent = extentOrFail(context, record.span, "index expression");
      const bracket = openingBracketOf(context, extent);
      if (bracket === null) fail(context, "cannot find the `[` of the index expression");
      const object = context.source.slice(extent.start, bracket);
      context.edits.push(point(bracket + 1, `__dv.checkIndex(${object}, `, context));
      context.edits.push(point(extent.end - 1, `, ${quote(loc)})`, context));
      break;
    }
    case "slice": {
      const node = expressionAt(
        context,
        index,
        record,
        (expression) =>
          expression.kind === "Call" &&
          expression.callee.kind === "Member" &&
          expression.callee.property === "slice",
      );
      if (node.kind !== "Call") {
        fail(context, "the slice obligation does not point at an `a.slice(i, j)` call", record.span);
      }
      const callee = node.callee;
      if (callee.kind !== "Member") {
        fail(context, "the slice obligation does not point at an `a.slice(i, j)` call", record.span);
      }
      const receiver: A.MemberExpr = callee;
      const call = node;
      if (call.args.length !== 2) {
        fail(context, `a slice check needs \`a.slice(i, j)\`, found ${call.args.length} argument(s)`);
      }
      const extent = extentOrFail(context, record.span, "slice call");
      if (context.source[extent.end - 1] !== ")") fail(context, "the slice call does not end with `)`");
      const object = sourceOfExtent(context, receiver.object.span, "slice receiver");
      const first = sourceOfExtent(context, call.args[0]!.span, "slice start");
      const second = sourceOfExtent(context, call.args[1]!.span, "slice end");
      const before = context.source.slice(extent.start, extent.end - 1);
      const comma = /\s*,\s*$/.test(before) ? "" : ", ";
      context.edits.push(
        point(extent.end - 1, `${comma}__dv.checkSlice(${object}, ${first}, ${second}, ${quote(loc)})`, context),
      );
      break;
    }
    case "append-length": {
      expressionAt(context, index, record, () => true);
      const extent = extentOrFail(context, record.span, "appended array");
      context.edits.push(wrap(extent.start, extent.end, "__dv.checkLength(", `, ${quote(loc)})`, context));
      break;
    }
    case "range": {
      expressionAt(context, index, record, () => true);
      const extent = extentOrFail(context, record.span, "arithmetic expression");
      context.edits.push(wrap(extent.start, extent.end, "__dv.checkRange(", `, ${quote(loc)})`, context));
      break;
    }
    case "pre-call": {
      const call = callAt(context, index, record);
      if (call.callee.kind === "Member") break; // a prelude built-in: it has no user preconditions
      const callee = calleeSpec(context, call, record);
      if (callee.preTexts.length === 0) break; // the callee has no `@pre` to check
      const args = argumentTexts(context, call);
      const conditions = callee.preTexts.map((text) => `(${substituteArguments(text, callee.params, args, context.path)})`);
      const text = callee.preTexts.join(" && ");
      const extent = extentOrFail(context, call.span, "call");
      const check = `__dv.checkPre(${conditions.join(" && ")}, ${quote(callee.name)}, ${quote(text)}, ${quote(loc)})`;
      context.edits.push(wrap(extent.start, extent.end, `(${check}, `, `)`, context));
      break;
    }
    case "measure-nonneg":
    case "measure-decrease": {
      const call = callAt(context, index, record);
      const callee = calleeSpec(context, call, record);
      if (callee.decreases === undefined) {
        fail(context, `cannot find a \`@decreases\` measure for the call the plan points at`);
      }
      const args = argumentTexts(context, call);
      const next = `(${substituteArguments(callee.decreases, callee.params, args, context.path)})`;
      const current = `(${callee.decreases})`;
      const text = quote(`@decreases ${callee.decreases}`);
      const check =
        record.kind === "measure-decrease"
          ? `__dv.checkCallMeasureDecrease(${next}, ${current}, ${quote(loc)})`
          : `__dv.checkMeasure(${next}, ${quote(callee.name)}, ${text}, ${quote(loc)})`;
      const extent = extentOrFail(context, call.span, "recursive call");
      context.edits.push(wrap(extent.start, extent.end, `(${check}, `, `)`, context));
      break;
    }
    default:
      break;
  }
}

function requireSpecText(context: Context, record: InjectionRecord): string {
  const text = record.specText.trim();
  if (text === "") {
    fail(context, `the ${record.kind} check has no spec text to evaluate`, record.span);
  }
  return text;
}

// ---------------------------------------------------------------------------
// Source ranges
// ---------------------------------------------------------------------------

const OPENERS: ReadonlySet<string> = new Set(["(", "[", "{"]);
const CLOSERS: ReadonlySet<string> = new Set([")", "]", "}"]);
const MATCHING_OPENER: Readonly<Record<string, string>> = { ")": "(", "]": "[", "}": "{" };

/**
 * The widest text region that is a syntactically complete expression starting at the span's
 * start.  Expression spans exclude grouping parentheses (`(x + y) * 2` is stored as
 * `x + y) * 2`), so unmatched brackets are closed by widening the region over the brackets
 * that belong to it.  Returns `null` when the region cannot be completed.
 */
function extentOf(context: Context, start: number, end: number): { start: number; end: number } | null {
  const source = context.source;
  const stack: string[] = [];
  let missingOpeners = 0;
  for (const token of context.tokens) {
    if (token.kind !== "punct") continue;
    const at = token.span.offset;
    if (at < start || at >= end) continue;
    if (OPENERS.has(token.text)) stack.push(token.text);
    else if (CLOSERS.has(token.text)) {
      const top = stack.pop();
      if (top === undefined) missingOpeners += 1;
      else if (top !== MATCHING_OPENER[token.text]) return null;
    }
  }
  if (stack.length > 0 && missingOpeners > 0) return null;
  let widenedEnd = end;
  for (let i = stack.length - 1; i >= 0; i -= 1) {
    widenedEnd = skipForward(source, widenedEnd);
    const closer = closerFor(stack[i]!);
    if (source[widenedEnd] !== closer) return null;
    widenedEnd += 1;
  }
  let widenedStart = start;
  for (let i = 0; i < missingOpeners; i += 1) {
    widenedStart = skipBackward(source, widenedStart);
    if (widenedStart === 0 || !OPENERS.has(source[widenedStart - 1]!)) return null;
    widenedStart -= 1;
  }
  if (!balanced(context, widenedStart, widenedEnd)) return null;
  return { start: widenedStart, end: widenedEnd };
}

function balanced(context: Context, start: number, end: number): boolean {
  const stack: string[] = [];
  for (const token of context.tokens) {
    if (token.kind !== "punct") continue;
    const at = token.span.offset;
    if (at < start || at >= end) continue;
    if (OPENERS.has(token.text)) stack.push(token.text);
    else if (CLOSERS.has(token.text)) {
      const top = stack.pop();
      if (top === undefined || top !== MATCHING_OPENER[token.text]) return false;
    }
  }
  return stack.length === 0;
}

/** The offset of the `[` that matches the `]` ending the region (`a[i]` → the `[`). */
function openingBracketOf(context: Context, extent: { start: number; end: number }): number | null {
  const close = extent.end - 1;
  if (context.source[close] !== "]") return null;
  let depth = 0;
  let found: number | null = null;
  for (const token of context.tokens) {
    if (token.kind !== "punct") continue;
    const at = token.span.offset;
    if (at < extent.start || at > close) continue;
    if (token.text === "[") {
      depth += 1;
      found = at;
    } else if (token.text === "]") {
      depth -= 1;
      if (depth === 0 && at === close) return found;
    }
  }
  return null;
}

function extentOrFail(context: Context, span: Span, what: string): { start: number; end: number } {
  const extent = extentOf(context, span.offset, span.endOffset ?? span.offset);
  if (extent === null) {
    fail(context, `the ${what} at ${location(span)} is not a complete expression; refusing to inject around it`, span);
  }
  return extent;
}

function sourceOfExtent(context: Context, span: Span, what: string): string {
  const extent = extentOrFail(context, span, what);
  return context.source.slice(extent.start, extent.end);
}

function skipForward(source: string, at: number): number {
  let i = at;
  while (i < source.length && /\s/.test(source[i]!)) i += 1;
  return i;
}

function skipBackward(source: string, at: number): number {
  let i = at;
  while (i > 0 && /\s/.test(source[i - 1]!)) i -= 1;
  return i;
}

function closerFor(opener: string): string {
  return opener === "(" ? ")" : opener === "[" ? "]" : "}";
}

// ---------------------------------------------------------------------------
// The function's AST
// ---------------------------------------------------------------------------

interface FunctionIndex {
  readonly returns: A.ReturnStmt[];
  readonly expressions: A.Expr[];
  readonly expressionAt: Map<number, A.Expr[]>;
  readonly loopAt: Map<number, A.WhileStmt | A.ForStmt>;
}

function buildIndex(body: A.BlockStmt): FunctionIndex {
  const returns: A.ReturnStmt[] = [];
  const expressions: A.Expr[] = [];
  const loopAt = new Map<number, A.WhileStmt | A.ForStmt>();
  const visitExpr = (expression: A.Expr): void => {
    expressions.push(expression);
    for (const child of childExpressions(expression)) visitExpr(child);
  };
  const visitStmt = (statement: A.Stmt): void => {
    switch (statement.kind) {
      case "VarDecl":
        for (const declarator of statement.declarations) if (declarator.init !== undefined) visitExpr(declarator.init);
        break;
      case "ExprStmt":
        visitExpr(statement.expr);
        break;
      case "If":
        visitExpr(statement.test);
        visitStmt(statement.then);
        if (statement.alternate !== null) visitStmt(statement.alternate);
        break;
      case "Return":
        returns.push(statement);
        if (statement.argument !== null) visitExpr(statement.argument);
        break;
      case "Switch":
        visitExpr(statement.discriminant);
        for (const switchCase of statement.cases) {
          if (switchCase.test !== null) visitExpr(switchCase.test);
          for (const inner of switchCase.body) visitStmt(inner);
        }
        break;
      case "While":
        loopAt.set(statement.span.offset, statement);
        visitExpr(statement.test);
        visitStmt(statement.body);
        break;
      case "For":
        loopAt.set(statement.span.offset, statement);
        if (statement.init !== null) visitStmt(statement.init);
        if (statement.test !== null) visitExpr(statement.test);
        if (statement.update !== null) visitExpr(statement.update);
        visitStmt(statement.body);
        break;
      case "Block":
        for (const inner of statement.body) visitStmt(inner);
        break;
      case "Throw":
        visitExpr(statement.argument);
        break;
      default:
        break;
    }
  };
  for (const statement of body.body) visitStmt(statement);
  const expressionAt = new Map<number, A.Expr[]>();
  for (const expression of expressions) {
    const list = expressionAt.get(expression.span.offset);
    if (list === undefined) expressionAt.set(expression.span.offset, [expression]);
    else list.push(expression);
  }
  return { returns, expressions, expressionAt, loopAt };
}

function childExpressions(expression: A.Expr): A.Expr[] {
  switch (expression.kind) {
    case "ArrayLit":
      return [...expression.elements];
    case "ObjectLit":
      return expression.props.flatMap((prop) => (prop.kind === "SpreadProp" ? [prop.expr] : [prop.value]));
    case "Template":
      return expression.parts.flatMap((part) => (part.type === "expr" ? [part.expr] : []));
    case "Member":
      return [expression.object];
    case "Index":
      return [expression.object, expression.index];
    case "Call":
      return [expression.callee, ...expression.args];
    case "New":
      return expression.args === null ? [expression.callee] : [expression.callee, ...expression.args];
    case "Unary":
      return [expression.operand];
    case "Update":
      return [expression.operand];
    case "Binary":
    case "Logical":
      return [expression.left, expression.right];
    case "Assign":
      return [expression.target, expression.value];
    case "Cond":
      return [expression.test, expression.consequent, expression.alternate];
    case "As":
      return [expression.expr];
    case "NonNull":
      return [expression.expr];
    case "Spread":
      return [expression.expr];
    case "Await":
      return [expression.expr];
    case "Yield":
      return expression.argument === null ? [] : [expression.argument];
    case "Seq":
      return [...expression.exprs];
    default:
      return [];
  }
}

function expressionAt(
  context: Context,
  index: FunctionIndex,
  record: InjectionRecord,
  predicate: (expression: A.Expr) => boolean,
): A.Expr {
  const candidates = (index.expressionAt.get(record.span.offset) ?? []).filter(predicate);
  if (candidates.length === 0) {
    fail(
      context,
      `the ${record.kind} obligation points at ${location(record.span)}, which is not ` +
        `the kind of expression the plan describes`,
      record.span,
    );
  }
  const exact = candidates.find(
    (candidate) => (candidate.span.endOffset ?? candidate.span.offset) === (record.span.endOffset ?? record.span.offset),
  );
  return exact ?? candidates[0]!;
}

function callAt(context: Context, index: FunctionIndex, record: InjectionRecord): A.CallExpr {
  return expressionAt(context, index, record, (expression) => expression.kind === "Call") as A.CallExpr;
}

// ---------------------------------------------------------------------------
// Callee specs: `@pre` and `@decreases` with the call's arguments substituted
// ---------------------------------------------------------------------------

interface CalleeSpec {
  readonly name: string;
  readonly params: readonly string[];
  readonly preTexts: readonly string[];
  readonly decreases?: string;
}

function calleeSpec(context: Context, call: A.CallExpr, record: InjectionRecord): CalleeSpec {
  if (call.callee.kind !== "Ident") {
    fail(context, `the plan points at a call whose callee is not a plain name`, record.span);
  }
  const name = call.callee.name;
  const local = context.parsed.functions.find((fn) => fn.name === name);
  if (local !== undefined) return specOf(local);
  const imported = importedDeclaration(context, name);
  if (imported === undefined) {
    fail(context, `cannot find the declaration of \`${name}\` to inject its precondition check`, record.span);
  }
  return specOf(imported);
}

function specOf(decl: A.FnDecl): CalleeSpec {
  const decreases = decreasesTag(decl);
  return {
    name: decl.name,
    params: decl.params.map((param) => param.name),
    preTexts: preTags(decl),
    ...(decreases === undefined ? {} : { decreases }),
  };
}

function preTags(decl: A.FnDecl): string[] {
  return decl.jsdoc === null ? [] : tagsNamed(decl.jsdoc, "pre").map((tag: JSDocTag) => tag.text);
}

function decreasesTag(decl: A.FnDecl): string | undefined {
  if (decl.jsdoc === null) return undefined;
  const tags = tagsNamed(decl.jsdoc, "decreases");
  return tags.length === 0 ? undefined : tags[0]!.text;
}

/** The declaration of an imported callee, parsed from its file (never imported). */
function importedDeclaration(context: Context, localName: string): A.FnDecl | undefined {
  for (const declaration of context.parsed.imports) {
    const binding = declaration.bindings.find((candidate) => candidate.local === localName);
    if (binding === undefined) continue;
    const target = resolveImportPath(context.path, declaration.specifier);
    if (target === null) return undefined;
    let parsed = context.calleeCache.get(target);
    if (parsed === undefined) {
      parsed = readParsed(context, target);
      context.calleeCache.set(target, parsed);
    }
    if (parsed === null) return undefined;
    return parsed.functions.find((fn) => fn.name === binding.imported);
  }
  return undefined;
}

function readParsed(context: Context, path: string): A.ParsedFile | null {
  const read = context.options.readFile ?? ((file: string) => readFileSync(file, "utf8"));
  try {
    return parseFile(path, read(path), { includeUnannotated: true });
  } catch {
    return null;
  }
}

/** The argument texts of a call, each a complete expression. */
function argumentTexts(context: Context, call: A.CallExpr): string[] {
  return call.args.map((argument) => sourceOfExtent(context, argument.span, "call argument"));
}

/**
 * Replace the callee's parameter names in a spec text with the call's arguments, so the
 * check can be evaluated in the caller.  Only identifier tokens are replaced, never strings.
 */
function substituteArguments(
  text: string,
  params: readonly string[],
  args: readonly string[],
  path: string,
): string {
  if (params.length === 0 || args.length === 0) return text;
  const tokens = lex(text, path).tokens;
  const out: string[] = [];
  let cursor = 0;
  for (let i = 0; i < tokens.length; i += 1) {
    const token = tokens[i]!;
    if (token.kind !== "ident") continue;
    const position = params.indexOf(token.text);
    if (position === -1 || position >= args.length) continue;
    const previous = tokens[i - 1];
    if (previous !== undefined && previous.kind === "punct" && previous.text === ".") continue;
    const next = tokens[i + 1];
    if (next !== undefined && next.kind === "punct" && next.text === ":") continue;
    out.push(text.slice(cursor, token.span.offset), `(${args[position]})`);
    cursor = token.span.endOffset ?? token.span.offset + token.text.length;
  }
  out.push(text.slice(cursor));
  return out.join("");
}

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

function location(span: Span): string {
  return `${span.file}:${span.line}:${span.col}`;
}

function quote(text: string): string {
  return JSON.stringify(text);
}
