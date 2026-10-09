/**
 * The differential-test driver (specification 6.8, milestone 9).
 *
 * For every certified function of one file it runs `count` generated inputs through **two**
 * implementations of the same source function:
 *
 *   - the original exported JS function, as Bun runs it (the plugin is active, so its
 *     injected guards, preconditions, postconditions and internal checks run too), and
 *   - the interpreter (`./interp.ts`) over `K.erase(term)` of the *kernel term the verifier
 *     certified* — the same term the trust story rests on.
 *
 * The results must be **deeply equal**, and every `@post` must hold on the original's
 * result.  Anything else is a failure with a diagnostic naming the function, the input, the
 * two results and (for a `@post`) the spec text: a disagreement means the elaboration (or
 * the injection, or the kernel) does not describe the code.
 *
 * `difftestFile` never throws for a mismatch; a mismatch is data (`report.failures`).  It
 * *can* throw when the file cannot be prepared at all (an unreadable import, say).
 */
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { contentHash } from "../extract/specs";
import {
  extractFile,
  type ExprIR,
  type FunctionIR,
  type TypeIR,
  type UnionIR,
} from "../extract/fragment";
import * as K from "../kernel/index";
import { verify } from "../verify";
import {
  DEFAULT_INPUT_COUNT,
  DEFAULT_MAX_ATTEMPTS,
  DEFAULT_SEED,
  evaluateSpec,
  generateInputs,
  specEnvFor,
  type InputObject,
  type InputValue,
} from "./gen";
import {
  GlobalTable,
  decodeSum,
  encodeSum,
  interpTerm,
  isVector,
  pair,
  projectPath,
  proof,
  showValue,
  type IrValue,
} from "./interp";

/** Why one input failed. */
export type DifftestFailureKind =
  /** The two implementations returned different values. */
  | "mismatch"
  /** A `@post` does not hold on the original's result (or cannot be evaluated). */
  | "post"
  /** The original function threw (an injected check fired, or the input was unusable). */
  | "call"
  /** The interpreter threw (its evaluation budget ran out, say). */
  | "interpret"
  /** No input was generated for this function at all. */
  | "no-inputs";

export interface DifftestFailure {
  readonly function: string;
  readonly kind: DifftestFailureKind;
  /** The 0-based index of the input among the generated ones. */
  readonly index: number;
  /** The input as written for a human: `x = 5, lo = 0`. */
  readonly input: string;
  /** The argument values themselves. */
  readonly values: readonly InputValue[];
  /** The original's result (or the error it threw), rendered. */
  readonly original?: string;
  /** The interpreter's result (or the error it threw), rendered. */
  readonly interpreted?: string;
  /** The `@post` text, for kind `post`. */
  readonly spec?: string;
  readonly message: string;
}

export interface DifftestFunctionReport {
  readonly name: string;
  /** Inputs actually run through both implementations. */
  readonly cases: number;
  readonly attempts: number;
  readonly rejected: number;
  readonly givenUp: number;
  readonly failures: readonly DifftestFailure[];
}

/** A function the driver could not test, and why. */
export interface DifftestSkip {
  readonly name: string;
  readonly reason: string;
}

export interface DifftestReport {
  readonly path: string;
  readonly seed: number;
  readonly count: number;
  readonly functions: readonly DifftestFunctionReport[];
  readonly skipped: readonly DifftestSkip[];
  readonly failures: readonly DifftestFailure[];
  readonly ok: boolean;
}

/**
 * A rewrite of an elaborated term before it is interpreted.
 *
 * **Test-only hook**: the milestone-9 unfaithful-elaboration test uses it to introduce a
 * deliberate bug (swapping the branches of `abs`, say) and shows that the differential test
 * catches it.  Nothing in the driver or the verifier passes one.
 */
export type TermTamper = (name: string, term: K.Term) => K.Term;

export interface DifftestOptions {
  readonly seed?: number;
  /** How many inputs per function (the acceptance path uses 200). */
  readonly count?: number;
  readonly maxAttempts?: number;
  /** The interpreter's evaluation budget per input. */
  readonly maxSteps?: number;
  /** File reader, for the file and its imports; defaults to `node:fs`. */
  readonly readFile?: (path: string) => string;
  /** Test-only: rewrite an elaborated term before interpreting it. */
  readonly tamper?: TermTamper;
  /** Restrict the run to these functions. */
  readonly only?: readonly string[];
}

/** How many failures one function contributes to the report before they are only counted. */
export const MAX_REPORTED_FAILURES = 10;

// ---------------------------------------------------------------------------
// Preparing the two implementations
// ---------------------------------------------------------------------------

const verifyCache = new Map<string, ReturnType<typeof verify>>();

/** `verify(path, source)`, cached per (path, content) so several difftests share one run. */
function verifyOnce(path: string, source: string, readFile: (file: string) => string): ReturnType<typeof verify> {
  const key = `${path}#${contentHash(source)}`;
  const cached = verifyCache.get(key);
  if (cached !== undefined) return cached;
  const result = verify(path, source, { readFile });
  verifyCache.set(key, result);
  return result;
}

/**
 * The definitions `Const` names resolve to: every `def` of the file's own environment, plus
 * the definitions of the imported files it calls.
 *
 * `verify` admits an imported callee as an `external` declaration, which carries only its
 * *type*; an `external` has no value to interpret.  The imported file is verified in turn
 * and its own `def`s are registered, so `useClamp`'s `percent` can interpret its call to
 * the imported `clamp` (and the tamper hook sees that definition too).
 */
function collectGlobals(
  path: string,
  source: string,
  options: DifftestOptions,
  readFile: (file: string) => string,
): { globals: GlobalTable; verifyResult: ReturnType<typeof verify> } {
  const globals = new GlobalTable();
  const visited = new Set<string>();
  let root: ReturnType<typeof verify> | undefined;

  const absorb = (file: string, text: string, depth: number): void => {
    const resolved = file;
    if (visited.has(resolved) || depth > 8) return;
    visited.add(resolved);
    const result = verifyOnce(resolved, text, readFile);
    if (resolved === path) root = result;
    for (const name of result.env.order) {
      const decl = result.env.decls.get(name);
      if (decl === undefined || decl.kind !== "def") continue;
      globals.define(name, options.tamper === undefined ? decl.value : options.tamper(name, decl.value));
    }
    for (const external of result.externals) {
      let imported: string;
      try {
        imported = readFile(external.file);
      } catch {
        continue;
      }
      absorb(external.file, imported, depth + 1);
    }
  };

  absorb(path, source, 0);
  if (root === undefined) throw new Error(`difftest: ${path} was not verified`);
  return { globals, verifyResult: root };
}

// ---------------------------------------------------------------------------
// JS values <-> interpreted values
// ---------------------------------------------------------------------------

/** A kernel-level value for a generated JS argument of `type`. */
function argumentValue(type: TypeIR, value: InputValue): IrValue {
  switch (type.kind) {
    case "int":
    case "generic":
      return typeof value === "number" ? BigInt(value) : proof;
    case "boolean":
      return typeof value === "boolean" ? value : proof;
    case "vec":
      return isVectorInput(value) ? value.map((element) => argumentValue(type.elem!, element)) : proof;
    case "union":
      return encodeUnion(type.union!, value);
  }
}

function isVectorInput(value: InputValue): value is readonly InputValue[] {
  return Array.isArray(value);
}

function isObjectInput(value: InputValue): value is InputObject {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

/**
 * A union value as the kernel encodes it: variant `i` of a `Sum` in declaration order, each
 * variant a nested `Sigma` record of its fields, with an `InRange` component after every
 * `number` field, terminated by `Unit` (`fragment.ts`'s `buildRecord`).
 */
function encodeUnion(union: UnionIR, value: InputValue): IrValue {
  if (!isObjectInput(value)) return proof;
  const tag = value[union.discriminant];
  const variant = union.variants.find((candidate) => candidate.tag === tag);
  if (variant === undefined) return proof;
  const components: IrValue[] = [];
  for (const field of variant.fields) {
    components.push(argumentValue(field.type, value[field.name] ?? proof));
    if (field.type.kind === "int") components.push(proof);
  }
  let record: IrValue = proof;
  for (let i = components.length - 1; i >= 0; i -= 1) record = pair(components[i]!, record);
  return encodeSum(variant.index, union.variants.length, record);
}

/** One interpreter argument per binder of the function's term telescope. */
export function interpreterArguments(fn: FunctionIR, values: readonly InputValue[]): IrValue[] {
  const byId = new Map<number, IrValue>();
  fn.params.forEach((param, index) => {
    const value = values[index] ?? proof;
    byId.set(param.binder.id, argumentValue(param.type, value));
    for (const extra of param.extra) {
      // The length companion of a vector parameter is the array's length: `len` reduces to
      // it, and `a.length` denotes it.
      byId.set(extra.id, extra.role === "vec-len" && isVectorInput(value) ? BigInt(value.length) : proof);
    }
  });
  return fn.signature.binders.map((binder) => byId.get(binder.id) ?? proof);
}

const SAFE_MAX = K.SAFE_MAX;
const SAFE_MIN = -K.SAFE_MAX;

/** The user-visible part of an interpreted result.  Out-of-range integers stay bigints. */
export function surfaceValue(value: IrValue, type: TypeIR): unknown {
  switch (type.kind) {
    case "int":
    case "generic":
      return typeof value === "bigint" && (value < SAFE_MIN || value > SAFE_MAX) ? value : bigintToJs(value);
    case "boolean":
      return value;
    case "vec":
      return isVector(value) ? value.map((element) => surfaceValue(element, type.elem!)) : showValue(value);
    case "union":
      return decodeUnion(type.union!, value);
  }
}

function bigintToJs(value: IrValue): unknown {
  return typeof value === "bigint" ? Number(value) : showValue(value);
}

function decodeUnion(union: UnionIR, value: IrValue): unknown {
  const decoded = decodeSum(value, union.variants.length);
  if (decoded === undefined) return showValue(value);
  const variant = union.variants[decoded.index];
  if (variant === undefined) return showValue(value);
  const out: Record<string, unknown> = { [union.discriminant]: variant.tag };
  for (const field of variant.fields) {
    out[field.name] = surfaceValue(projectPath(decoded.payload, field.path), field.type);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Comparison
// ---------------------------------------------------------------------------

/**
 * Structural equality of a JS value and an interpreted one.  A `bigint` never equals a
 * `number` (an interpreted integer outside the safe range is a mismatch, not a rounding
 * artefact), and arrays and objects compare structurally.
 */
export function deepEqual(left: unknown, right: unknown): boolean {
  if (typeof left === "bigint" || typeof right === "bigint") return left === right;
  if (Array.isArray(left) || Array.isArray(right)) {
    if (!Array.isArray(left) || !Array.isArray(right) || left.length !== right.length) return false;
    return left.every((element, index) => deepEqual(element, right[index]));
  }
  if (typeof left === "object" && left !== null && typeof right === "object" && right !== null) {
    const leftKeys = Object.keys(left).sort();
    const rightKeys = Object.keys(right).sort();
    if (leftKeys.length !== rightKeys.length) return false;
    return leftKeys.every(
      (key, index) =>
        key === rightKeys[index] &&
        deepEqual((left as Record<string, unknown>)[key], (right as Record<string, unknown>)[key]),
    );
  }
  return left === right;
}

/** A readable rendering of a JS value, for a failure message. */
export function describeJs(value: unknown): string {
  if (value === undefined) return "undefined";
  if (typeof value === "bigint") return `${value}n`;
  if (typeof value === "string") return JSON.stringify(value);
  if (value === null || typeof value === "number" || typeof value === "boolean") return String(value);
  if (Array.isArray(value)) return `[${value.map(describeJs).join(", ")}]`;
  const entries = Object.entries(value as Record<string, unknown>).map(
    ([key, entry]) => `${key}: ${describeJs(entry)}`,
  );
  return `{${entries.join(", ")}}`;
}

/** `x = 5, lo = 0`, the input as a diagnostic writes it. */
export function describeInput(fn: FunctionIR, values: readonly InputValue[]): string {
  return fn.params.map((param, index) => `${param.name} = ${describeJs(values[index])}`).join(", ");
}

// ---------------------------------------------------------------------------
// Running one function
// ---------------------------------------------------------------------------

interface OriginalOutcome {
  readonly value?: unknown;
  readonly error?: string;
}

function callOriginal(
  original: (...args: unknown[]) => unknown,
  values: readonly InputValue[],
): OriginalOutcome {
  try {
    return { value: original(...(values as unknown[])) };
  } catch (error) {
    return { error: error instanceof Error ? `${error.name}: ${error.message}` : String(error) };
  }
}

/**
 * The `@post` texts that do not hold on `result` (or cannot be evaluated at all).  This is
 * the `@post` half of the differential test: the postcondition is evaluated against the
 * parameters and the *original* function's result.
 */
export function failingPostconditions(
  fn: FunctionIR,
  values: readonly InputValue[],
  result: unknown,
): { spec: string }[] {
  const env = specEnvFor(fn, values, result as InputValue);
  const out: { spec: string }[] = [];
  for (const post of fn.signature.result.posts) {
    if (evaluateSpec(post.prop, env) !== true) {
      out.push({ spec: post.text ?? renderPost(post.prop) });
    }
  }
  return out;
}

/** A fallback rendering of a spec expression, when the extractor recorded no text. */
function renderPost(prop: ExprIR): string {
  return `<post ${prop.kind}>`;
}

function failureMessage(
  fn: FunctionIR,
  index: number,
  values: readonly InputValue[],
  detail: string,
): string {
  return `\`${fn.name}\` input #${index} (${describeInput(fn, values)}): ${detail}`;
}

interface FunctionRun {
  readonly report: DifftestFunctionReport;
  readonly failures: DifftestFailure[];
}

function runFunction(
  fn: FunctionIR,
  term: K.ErasedTerm,
  original: (...args: unknown[]) => unknown,
  globals: GlobalTable,
  options: DifftestOptions,
  seed: number,
  count: number,
): FunctionRun {
  const run = interpTerm(term, { globals, ...(options.maxSteps === undefined ? {} : { maxSteps: options.maxSteps }) });
  const generated = generateInputs(fn, {
    seed,
    count,
    maxAttempts: options.maxAttempts ?? DEFAULT_MAX_ATTEMPTS,
  });
  const failures: DifftestFailure[] = [];
  let cases = 0;
  const report = (failure: DifftestFailure): void => {
    failures.push(failure);
  };
  const kept = (): DifftestFailure[] => failures.slice(0, MAX_REPORTED_FAILURES);

  for (const [index, values] of generated.inputs.entries()) {
    cases += 1;
    const originalOutcome = callOriginal(original, values);
    let interpreted: unknown;
    let interpretedError: string | undefined;
    try {
      interpreted = surfaceValue(
        projectPath(
          run(interpreterArguments(fn, values)),
          fn.signature.result.layout.valuePath,
        ),
        fn.signature.result.type,
      );
    } catch (error) {
      interpretedError = error instanceof Error ? `${error.name}: ${error.message}` : String(error);
    }

    if (originalOutcome.error !== undefined) {
      report({
        function: fn.name,
        kind: "call",
        index,
        input: describeInput(fn, values),
        values,
        original: originalOutcome.error,
        ...(interpretedError === undefined ? { interpreted: describeJs(interpreted) } : { interpreted: interpretedError }),
        message: failureMessage(fn, index, values, `the original threw ${originalOutcome.error}`),
      });
      continue;
    }
    if (interpretedError !== undefined) {
      report({
        function: fn.name,
        kind: "interpret",
        index,
        input: describeInput(fn, values),
        values,
        original: describeJs(originalOutcome.value),
        interpreted: interpretedError,
        message: failureMessage(fn, index, values, `the interpreter threw ${interpretedError}`),
      });
      continue;
    }
    if (!deepEqual(originalOutcome.value, interpreted)) {
      report({
        function: fn.name,
        kind: "mismatch",
        index,
        input: describeInput(fn, values),
        values,
        original: describeJs(originalOutcome.value),
        interpreted: describeJs(interpreted),
        message: failureMessage(
          fn,
          index,
          values,
          `the original returned ${describeJs(originalOutcome.value)}, the interpreter returned ${describeJs(interpreted)}`,
        ),
      });
    }
    const posts = failingPostconditions(fn, values, originalOutcome.value);
    for (const post of posts) {
      report({
        function: fn.name,
        kind: "post",
        index,
        input: describeInput(fn, values),
        values,
        original: describeJs(originalOutcome.value),
        interpreted: describeJs(interpreted),
        spec: post.spec,
        message: failureMessage(
          fn,
          index,
          values,
          `postcondition \`${post.spec}\` does not hold for result = ${describeJs(originalOutcome.value)}`,
        ),
      });
    }
  }

  if (cases === 0) {
    report({
      function: fn.name,
      kind: "no-inputs",
      index: 0,
      input: "",
      values: [],
      message: `\`${fn.name}\`: no input satisfied every \`@pre\` within ${options.maxAttempts ?? DEFAULT_MAX_ATTEMPTS} attempts`,
    });
  }
  return {
    report: {
      name: fn.name,
      cases,
      attempts: generated.attempts,
      rejected: generated.rejected,
      givenUp: generated.givenUp,
      failures: kept(),
    },
    failures,
  };
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/**
 * Differential-test every certified function of `path`.
 *
 * The file is verified (cached by content), the original module is imported (through the
 * Bun plugin, so its injected checks run), and `count` inputs per function go through the
 * original and the interpreter of the kernel term the verifier certified.
 */
export async function difftestFile(path: string, options: DifftestOptions = {}): Promise<DifftestReport> {
  const readFile = options.readFile ?? ((file: string) => readFileSync(file, "utf8"));
  const source = readFile(path);
  const ir = extractFile(path, source);
  const { globals, verifyResult } = collectGlobals(path, source, options, readFile);
  const verdicts = new Map(verifyResult.functions.map((fn) => [fn.name, fn]));
  const seed = options.seed ?? DEFAULT_SEED;
  const count = options.count ?? DEFAULT_INPUT_COUNT;
  const functions: DifftestFunctionReport[] = [];
  const skipped: DifftestSkip[] = [];
  const failures: DifftestFailure[] = [];

  const module = (await import(pathToFileURL(path).href)) as Record<string, unknown>;
  let index = 0;
  for (const fn of ir.functions) {
    if (options.only !== undefined && !options.only.includes(fn.name)) continue;
    const verdict = verdicts.get(fn.name);
    const term = globals.get(fn.name);
    const exported = module[fn.name];
    if (verdict?.status !== "certified" || term === undefined) {
      skipped.push({ name: fn.name, reason: `not kernel-certified (${verdict?.status ?? "unknown"})` });
      continue;
    }
    if (typeof exported !== "function") {
      skipped.push({ name: fn.name, reason: `the module does not export a function named \`${fn.name}\`` });
      continue;
    }
    // Each function gets its own stream, so adding a function does not shift the others.
    const result = runFunction(
      fn,
      term,
      exported as (...args: unknown[]) => unknown,
      globals,
      options,
      seed + index,
      count,
    );
    index += 1;
    functions.push(result.report);
    failures.push(...result.failures);
  }

  return {
    path,
    seed,
    count,
    functions,
    skipped,
    failures,
    ok: failures.length === 0 && functions.every((fn) => fn.cases > 0),
  };
}

/** A readable, multi-line summary of a report: one line per failing input. */
export function formatDifftestReport(report: DifftestReport): string {
  const lines = [
    `difftest ${report.path}: ${report.ok ? "ok" : "FAILED"} ` +
      `(${report.functions.length} function(s), ${report.functions.reduce((sum, fn) => sum + fn.cases, 0)} input(s), seed ${report.seed})`,
  ];
  for (const fn of report.functions) {
    lines.push(
      `  ${fn.name}: ${fn.cases} input(s), ${fn.failures.length} failure(s)` +
        (fn.givenUp === 0 ? "" : `, ${fn.givenUp} input(s) given up`),
    );
  }
  for (const skip of report.skipped) lines.push(`  skipped ${skip.name}: ${skip.reason}`);
  for (const failure of report.failures.slice(0, MAX_REPORTED_FAILURES)) {
    lines.push(`  [${failure.kind}] ${failure.message}`);
  }
  if (report.failures.length > MAX_REPORTED_FAILURES) {
    lines.push(`  … ${report.failures.length - MAX_REPORTED_FAILURES} more failure(s)`);
  }
  return lines.join("\n");
}
