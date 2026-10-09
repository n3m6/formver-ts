/**
 * Runtime check helpers (specification 6.6).
 *
 * This module is **injected code**, not verifier code: `src/inject/inject.ts` makes every
 * verified file import it (or `Bun.build` bundles it) and calls the helpers below in place of
 * the obligations the kernel did not certify.  It therefore has **no dependencies at all** —
 * no `node:` imports, no kernel, no `Bun` global — so it can be bundled into any target.
 *
 * Every helper either returns the value it was given (so it can wrap an expression in place)
 * or throws one of the three error classes; a check never silently weakens a program.
 *
 * `number` means a *safe integer* (specification 3.4), so `guardInt` rejects floats, `NaN`,
 * `Infinity` and anything past `±(2^53 - 1)`, and `guardIntArray` checks **every element**
 * (O(n), the documented cost of an exported `readonly number[]` parameter).
 */

/** 2^53 - 1: the largest safe integer, the model of `number`. */
export const SAFE_MAX: number = 9007199254740991;

/** 2^32 - 1: JavaScript's maximum array length, the kernel's `Vec` bound. */
export const MAX_VEC_LEN: number = 4294967295;

/** The values a check reports when it fails: the parameters in scope (and `result`). */
export type ArgSnapshot = Readonly<Record<string, unknown>>;

/** A `file:line:col` location parsed apart. */
export interface CheckLocation {
  readonly file: string;
  readonly line: number;
  readonly col: number;
}

/** Parse a `file:line:col` string; `undefined` for anything else (a guard has no location). */
export function parseLocation(loc: string | undefined): CheckLocation | undefined {
  if (loc === undefined) return undefined;
  const match = /^(.*):(\d+):(\d+)$/.exec(loc);
  if (match === null) return undefined;
  return { file: match[1]!, line: Number(match[2]), col: Number(match[3]) };
}

/** A short rendering of one snapshot entry (arrays are summarized, not dumped). */
export function describeArgument(value: unknown): string {
  if (Array.isArray(value)) return `[${value.length} element${value.length === 1 ? "" : "s"}]`;
  if (typeof value === "string") return JSON.stringify(value);
  if (typeof value === "number" || typeof value === "boolean" || value === null || value === undefined) {
    return String(value);
  }
  return Object.prototype.toString.call(value);
}

function describeArguments(args: ArgSnapshot): string {
  const entries = Object.entries(args);
  if (entries.length === 0) return "";
  return ` (${entries.map(([name, value]) => `${name} = ${describeArgument(value)}`).join(", ")})`;
}

/**
 * The common base of the three errors: the function, the spec text, the argument snapshot
 * and the injected `file:line:col` location.  `name` is the concrete class name, so
 * `error.name` and `instanceof` agree.
 */
export class RuntimeCheckError extends Error {
  /** The verified function the check belongs to (`""` when only the location identifies it). */
  readonly fn: string;
  /** The spec expression as written in the source (or the guard's type text). */
  readonly spec: string;
  /** The arguments in scope when the check failed. */
  readonly args: ArgSnapshot;
  /** `file:line:col` of the check, when the helper was given one. */
  readonly loc?: string;
  readonly file?: string;
  readonly line?: number;
  readonly col?: number;

  constructor(name: string, kind: string, fn: string, spec: string, args: ArgSnapshot, loc?: string) {
    const where = loc === undefined ? "" : ` at ${loc}`;
    const what = fn === "" ? kind : `${fn}: ${kind}`;
    super(`${what} \`${spec}\` failed${where}${describeArguments(args)}`);
    this.name = name;
    this.fn = fn;
    this.spec = spec;
    this.args = args;
    this.loc = loc;
    const parsed = parseLocation(loc);
    if (parsed !== undefined) {
      this.file = parsed.file;
      this.line = parsed.line;
      this.col = parsed.col;
    }
  }
}

/** A `@pre` (or a call-site precondition) that did not hold. */
export class PreconditionError extends RuntimeCheckError {
  constructor(fn: string, spec: string, args: ArgSnapshot, loc?: string) {
    super("PreconditionError", "precondition", fn, spec, args, loc);
  }
}

/** A `@post` that did not hold for the value a `return` produced. */
export class PostconditionError extends RuntimeCheckError {
  constructor(fn: string, spec: string, args: ArgSnapshot, loc?: string) {
    super("PostconditionError", "postcondition", fn, spec, args, loc);
  }
}

/**
 * A boundary guard, an index/slice/range/append check, a loop invariant or a termination
 * measure that did not hold.  `kind` is the obligation kind (`"guard"`, `"index"`, …).
 */
export class ObligationError extends RuntimeCheckError {
  readonly kind: string;

  constructor(kind: string, fn: string, spec: string, args: ArgSnapshot, loc?: string) {
    super("ObligationError", `${kind} check`, fn, spec, args, loc);
    this.kind = kind;
  }
}

// ---------------------------------------------------------------------------
// Boundary guards (exported parameters; always kept, in every mode)
// ---------------------------------------------------------------------------

/** `number` boundary guard: a safe integer. */
export function guardInt(name: string, param: string, value: unknown): number {
  if (typeof value !== "number" || !Number.isSafeInteger(value)) {
    throw new ObligationError("guard", name, `${param}: number`, { [param]: value });
  }
  return value;
}

function summarizeArray(value: readonly unknown[]): unknown {
  return value.length <= 8 ? value : `[${value.length} elements]`;
}

/** `readonly number[]` boundary guard: an array whose **every** element is a safe integer. */
export function guardIntArray(name: string, param: string, value: unknown): readonly number[] {
  if (!Array.isArray(value)) {
    throw new ObligationError("guard", name, `${param}: readonly number[]`, { [param]: value });
  }
  const array = value as readonly unknown[];
  for (let i = 0; i < array.length; i += 1) {
    const element = array[i];
    if (typeof element !== "number" || !Number.isSafeInteger(element)) {
      throw new ObligationError("guard", name, `${param}: readonly number[]`, {
        [param]: summarizeArray(array),
        index: i,
        element,
      });
    }
  }
  return value as readonly number[];
}

/** `readonly T[]` boundary guard: an array within JavaScript's length limit. */
export function guardArray(name: string, param: string, value: unknown): readonly unknown[] {
  if (!Array.isArray(value)) {
    throw new ObligationError("guard", name, `${param}: readonly T[]`, { [param]: value });
  }
  const array = value as readonly unknown[];
  if (array.length > MAX_VEC_LEN) {
    throw new ObligationError("guard", name, `${param}: readonly T[]`, { [param]: summarizeArray(array) });
  }
  return array;
}

/**
 * A tagged-union boundary guard.  The helper only knows the parameter name, not the union's
 * discriminant, so it checks what a boundary can check cheaply: the value is an object (so
 * `value.kind` cannot throw a `TypeError`).  Field-level guarantees come from the caller's
 * verification, exactly as for a union returned by a verified function.
 */
export function guardUnion(name: string, param: string, value: unknown): unknown {
  if (typeof value !== "object" || value === null) {
    throw new ObligationError("guard", name, `${param}: union`, { [param]: value });
  }
  return value;
}

// ---------------------------------------------------------------------------
// Internal obligation checks (wrapped in place, or at a loop head)
// ---------------------------------------------------------------------------

/** Check `0 <= i < a.length` and return `i`, so it can wrap an index expression. */
export function checkIndex(a: readonly unknown[], i: number, loc: string): number {
  if (a === null || a === undefined || !Number.isSafeInteger(i) || i < 0 || i >= a.length) {
    throw new ObligationError("index", "", "0 <= i && i < a.length", { i, "a.length": a?.length }, loc);
  }
  return i;
}

/** Check that an arithmetic value is still a safe integer, and return it. */
export function checkRange(value: number, loc: string): number {
  if (typeof value !== "number" || !Number.isSafeInteger(value)) {
    throw new ObligationError("range", "", "InRange(value)", { value }, loc);
  }
  return value;
}

/** Check `0 <= i <= j <= a.length` and return `[i, j]`, to spread into `a.slice(i, j)`. */
export function checkSlice(a: readonly unknown[], i: number, j: number, loc: string): [number, number] {
  const length = a?.length;
  const ok =
    Number.isSafeInteger(i) &&
    Number.isSafeInteger(j) &&
    i >= 0 &&
    i <= j &&
    length !== undefined &&
    j <= length;
  if (!ok) {
    throw new ObligationError("slice", "", "0 <= i && i <= j && j <= a.length", { i, j, "a.length": length }, loc);
  }
  return [i, j];
}

/** Check that an appended array is within the maximum length, and return it. */
export function checkLength(value: readonly unknown[], loc: string): readonly unknown[] {
  if (!Array.isArray(value) || value.length > MAX_VEC_LEN) {
    throw new ObligationError("append-length", "", "a.length + b.length <= 4294967295", {
      length: Array.isArray(value) ? value.length : value,
    }, loc);
  }
  return value;
}

/** A call-site precondition check: throws `PreconditionError` and returns the condition. */
export function checkPre(condition: unknown, name: string, text: string, loc: string): boolean {
  if (!condition) throw new PreconditionError(name, text, {}, loc);
  return true;
}

/** A loop invariant (or a loop-head invariant) check. */
export function checkInvariant(predicate: unknown, name: string, text: string, loc: string): boolean {
  if (!predicate) throw new ObligationError("invariant", name, text, {}, loc);
  return true;
}

/** A termination measure check: a non-negative safe integer. */
export function checkMeasure(measure: number, name: string, text: string, loc: string): number {
  if (typeof measure !== "number" || !Number.isSafeInteger(measure) || measure < 0) {
    throw new ObligationError("measure-nonneg", name, text, { measure }, loc);
  }
  return measure;
}

/**
 * A loop decrease monitor.  A `while` body is a single point per iteration, so the helper
 * remembers the measure it saw at this source location and requires every later visit to be
 * strictly smaller (the first visit is the loop's initialization).  Injected only for loops
 * whose function is not recursive, so one activation of the loop can never overlap another.
 */
const measureMemory = new Map<string, number>();

export function checkMeasureDecrease(measure: number, name: string, text: string, loc: string): number {
  if (typeof measure !== "number" || !Number.isSafeInteger(measure) || measure < 0) {
    throw new ObligationError("measure-nonneg", name, text, { measure }, loc);
  }
  const previous = measureMemory.get(loc);
  measureMemory.set(loc, measure);
  if (previous !== undefined && measure >= previous) {
    throw new ObligationError("measure-decrease", name, text, { measure, previous }, loc);
  }
  return measure;
}

/** A stateless recursive-call measure check: `next < previous` (`next` already non-negative). */
export function checkCallMeasureDecrease(next: number, previous: number, loc: string): number {
  if (
    typeof next !== "number" ||
    !Number.isSafeInteger(next) ||
    next < 0 ||
    typeof previous !== "number" ||
    !Number.isSafeInteger(previous) ||
    next >= previous
  ) {
    throw new ObligationError("measure-decrease", "", "measure(call) < measure(entry)", { next, previous }, loc);
  }
  return next;
}
