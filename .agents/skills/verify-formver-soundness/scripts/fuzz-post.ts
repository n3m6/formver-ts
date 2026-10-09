#!/usr/bin/env bun
/**
 * Independent postcondition oracle for formver-ts.
 *
 * For every exported, annotated function in a file: generate random arguments, keep those
 * that satisfy all of its precondition tags, call the function, and evaluate each
 * postcondition tag on the result. Nothing here uses the verifier. Signatures and JSDoc tags
 * are read with regular expressions, spec text is evaluated as plain JavaScript through
 * `new Function`, and the function under test is whatever Bun loads. The verifier's model is
 * checked as well: a declared `number` result (or `number[]` element) must be a safe integer.
 *
 * Usage (prefer the wrapper, which picks the working directory and so the plugin mode):
 *   fuzz-post.sh [--with-plugin] <file.ts> [--fn name]... [--count N] [--seed S] [--gen gen.ts] [--json out.json]
 *
 * A --gen module default-exports `(fn: string, rng: Rng) => unknown[] | undefined`, where
 * Rng is `{ next(): number; int(lo, hi): number; pick(items): item; safeInt(): number }`.
 * Returning undefined falls back to the built-in generator for that function.
 *
 * Exit: 0 no violation; 1 a violation or an unexpected throw; 2 usage error or nothing testable.
 */
import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";

interface Rng {
  next(): number;
  int(lo: number, hi: number): number;
  pick<T>(items: readonly T[]): T;
  safeInt(): number;
}

type Kind = "int" | "bool" | "intArray" | "array" | "other";

interface Param {
  readonly name: string;
  readonly type: string;
  readonly kind: Kind;
}

interface FunctionSpec {
  readonly name: string;
  readonly params: readonly Param[];
  readonly returnType: string;
  readonly returnKind: Kind;
  readonly pre: readonly string[];
  readonly post: readonly string[];
}

interface Finding {
  readonly kind: "post" | "range" | "post-error" | "unexpected-throw";
  readonly spec?: string;
  readonly args: string;
  readonly result?: string;
  readonly error?: string;
}

interface FunctionReport {
  readonly name: string;
  readonly status: "tested" | "skipped";
  readonly reason?: string;
  generated: number;
  satisfied: number;
  preErrors: number;
  resourceThrows: number;
  readonly findings: Finding[];
}

const MAX = Number.MAX_SAFE_INTEGER;
const EDGES: readonly number[] = [
  0, 1, -1, 2, -2, 3, -3, 10, -10, 100, -100, 1000, -1000, 1_000_000, -1_000_000,
  2 ** 31 - 1, -(2 ** 31), 2 ** 32 - 1, 2 ** 32, 2 ** 52, -(2 ** 52), MAX, -MAX, MAX - 1, -MAX + 1,
];
const MAX_REPORTED = 5;

// ---------------------------------------------------------------------------
// Arguments
// ---------------------------------------------------------------------------

function parseArgs(argv: readonly string[]) {
  const options = { file: "", only: [] as string[], count: 300, seed: 1, gen: "", json: "" };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i]!;
    const value = (): string => {
      const next = argv[i + 1];
      if (next === undefined) usage(`${arg} needs a value`);
      i += 1;
      return next;
    };
    if (arg === "--fn") options.only.push(value());
    else if (arg === "--count") options.count = Number(value());
    else if (arg === "--seed") options.seed = Number(value());
    else if (arg === "--gen") options.gen = resolve(value());
    else if (arg === "--json") options.json = resolve(value());
    else if (arg.startsWith("--")) usage(`unknown option ${arg}`);
    else if (options.file === "") options.file = resolve(arg);
    else usage(`unexpected argument ${arg}`);
  }
  if (options.file === "") usage("missing <file.ts>");
  if (!Number.isInteger(options.count) || options.count < 1) usage("--count must be a positive integer");
  return options;
}

function usage(message: string): never {
  console.error(`fuzz-post: ${message}`);
  console.error("usage: fuzz-post.sh [--with-plugin] <file.ts> [--fn name]... [--count N] [--seed S] [--gen gen.ts] [--json out.json]");
  process.exit(2);
}

// ---------------------------------------------------------------------------
// Reading the file without the verifier
// ---------------------------------------------------------------------------

const FUNCTION =
  /\/\*\*((?:(?!\*\/)[\s\S])*)\*\/\s*export\s+function\s+([A-Za-z_$][\w$]*)\s*(?:<([^>]*)>)?\s*\(([^)]*)\)\s*:\s*([^{]+?)\s*\{/g;

function splitTopLevel(text: string, separator: string): string[] {
  const parts: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i]!;
    if ("<([{".includes(ch)) depth += 1;
    else if (">)]}".includes(ch)) depth -= 1;
    else if (depth === 0 && text.startsWith(separator, i)) {
      parts.push(text.slice(start, i));
      start = i + separator.length;
    }
  }
  parts.push(text.slice(start));
  return parts.map((part) => part.trim()).filter((part) => part !== "");
}

function classify(type: string, generics: readonly string[]): Kind {
  const t = type.replace(/\s+/g, " ").trim();
  if (t === "number") return "int";
  if (t === "boolean") return "bool";
  const element =
    /^(?:readonly )?([A-Za-z_$][\w$]*)\[\]$/.exec(t)?.[1] ??
    /^(?:ReadonlyArray|Array)<([A-Za-z_$][\w$]*)>$/.exec(t)?.[1];
  if (element === "number") return "intArray";
  if (element !== undefined && generics.includes(element)) return "array";
  return "other";
}

function specTags(comment: string): { pre: string[]; post: string[] } {
  const tags = { pre: [] as string[], post: [] as string[] };
  let current: string[] | undefined;
  for (const raw of comment.split("\n")) {
    const line = raw.replace(/^\s*\*?/, "").trim();
    const tag = /^@([A-Za-z]+)\s*(.*)$/.exec(line);
    if (tag !== null) {
      current = tag[1] === "pre" ? tags.pre : tag[1] === "post" ? tags.post : undefined;
      current?.push(tag[2]!.trim());
    } else if (line === "") {
      current = undefined;
    } else if (current !== undefined) {
      current[current.length - 1] += ` ${line}`;
    }
  }
  return tags;
}

function readFunctions(source: string): FunctionSpec[] {
  const functions: FunctionSpec[] = [];
  for (const match of source.matchAll(FUNCTION)) {
    const [, comment, name, genericText, paramText, returnType] = match;
    const generics = splitTopLevel(genericText ?? "", ",").map((g) => g.split(/\s+/)[0]!);
    const params = splitTopLevel(paramText!, ",").map((text): Param => {
      const parsed = /^([A-Za-z_$][\w$]*)\s*\??\s*:\s*([\s\S]+?)\s*(?:=\s*[\s\S]+)?$/.exec(text);
      const type = parsed?.[2] ?? "unknown";
      return { name: parsed?.[1] ?? text, type, kind: classify(type, generics) };
    });
    const tags = specTags(comment!);
    if (tags.pre.length === 0 && tags.post.length === 0) continue;
    functions.push({
      name: name!,
      params,
      returnType: returnType!.trim(),
      returnKind: classify(returnType!, generics),
      ...tags,
    });
  }
  return functions;
}

// ---------------------------------------------------------------------------
// Inputs
// ---------------------------------------------------------------------------

function makeRng(seed: number): Rng {
  let state = seed >>> 0;
  const next = (): number => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const int = (lo: number, hi: number): number => lo + Math.floor(next() * (hi - lo + 1));
  const pick = <T>(items: readonly T[]): T => items[Math.floor(next() * items.length)]!;
  const safeInt = (): number => {
    const magnitude = Math.min(Math.floor(next() * 2 ** 21) * 2 ** 32 + Math.floor(next() * 2 ** 32), MAX);
    return magnitude === 0 || next() < 0.5 ? magnitude : -magnitude;
  };
  return { next, int, pick, safeInt };
}

const clampSafe = (n: number): number => Math.max(-MAX, Math.min(MAX, n));

/** Small values, boundaries, and values next to earlier arguments (lengths and integers). */
function genInt(rng: Rng, related: readonly number[]): number {
  const r = rng.next();
  if (related.length > 0 && r < 0.25) return clampSafe(rng.pick(related) + rng.pick([-1, 0, 0, 1]));
  if (r < 0.4) return rng.pick(EDGES);
  if (r < 0.7) return rng.int(-10, 10);
  if (r < 0.85) return rng.int(-1000, 1000);
  if (r < 0.93) return rng.int(-1_000_000, 1_000_000);
  return rng.safeInt();
}

function genIntArray(rng: Rng): readonly number[] {
  const r = rng.next();
  const length = r < 0.1 ? 0 : r < 0.7 ? rng.int(1, 5) : r < 0.95 ? rng.int(6, 16) : rng.int(17, 64);
  const values = Array.from({ length }, () => (rng.next() < 0.7 ? rng.int(-10, 10) : genInt(rng, [])));
  if (rng.next() < 0.3) values.sort((a, b) => a - b);
  return Object.freeze(values);
}

function builtinArgs(fn: FunctionSpec, rng: Rng): unknown[] {
  const related: number[] = [];
  return fn.params.map((param) => {
    if (param.kind === "int") {
      const value = genInt(rng, related);
      related.push(value);
      return value;
    }
    if (param.kind === "bool") return rng.next() < 0.5;
    const array = genIntArray(rng);
    related.push(array.length);
    return array;
  });
}

// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

function describe(value: unknown): string {
  if (Array.isArray(value)) {
    const shown = value.slice(0, 20).map(describe).join(", ");
    return `[${shown}${value.length > 20 ? `, … (${value.length} elements)` : ""}]`;
  }
  if (typeof value === "number") return Object.is(value, -0) ? "-0" : String(value);
  if (typeof value === "string") return JSON.stringify(value);
  if (value !== null && typeof value === "object") {
    return `{ ${Object.entries(value).map(([k, v]) => `${k}: ${describe(v)}`).join(", ")} }`;
  }
  return String(value);
}

type Compiled = (scope: object, args: readonly unknown[], result: unknown) => unknown;

function compile(expression: string, params: readonly Param[]): Compiled {
  const body = `with (__scope) { return (${expression}); }`;
  const fn = new Function("__scope", ...params.map((p) => p.name), "result", body) as (...a: unknown[]) => unknown;
  return (scope, args, result) => fn(scope, ...args, result);
}

function inModel(kind: Kind, value: unknown): boolean {
  if (kind === "int") return Number.isSafeInteger(value);
  if (kind === "intArray") return Array.isArray(value) && value.every((v) => Number.isSafeInteger(v));
  if (kind === "array") return Array.isArray(value);
  return true;
}

function isResourceError(error: unknown): boolean {
  return error instanceof RangeError && /call stack|stack size/i.test(error.message);
}

async function main(): Promise<number> {
  const options = parseArgs(process.argv.slice(2));
  const source = readFileSync(options.file, "utf8");
  const functions = readFunctions(source).filter((fn) => options.only.length === 0 || options.only.includes(fn.name));
  const module = (await import(pathToFileURL(options.file).href)) as Record<string, unknown>;
  const scope = { ...module };
  const generator =
    options.gen === ""
      ? undefined
      : ((await import(pathToFileURL(options.gen).href)) as { default: (fn: string, rng: Rng) => unknown[] | undefined })
          .default;
  const rng = makeRng(options.seed);
  const mode = process.env["FUZZ_POST_MODE"] ?? "unknown (run through fuzz-post.sh)";

  console.log(`fuzz-post ${options.file}`);
  console.log(`  mode ${mode}, seed ${options.seed}, ${options.count} input(s) per function`);
  const reports: FunctionReport[] = [];

  for (const fn of functions) {
    const report: FunctionReport = {
      name: fn.name,
      status: "tested",
      generated: 0,
      satisfied: 0,
      preErrors: 0,
      resourceThrows: 0,
      findings: [],
    };
    const skip = (reason: string): void => {
      reports.push({ ...report, status: "skipped", reason });
      console.log(`  skipped ${fn.name}: ${reason}`);
    };
    const impl = module[fn.name];
    if (typeof impl !== "function") {
      skip("the module does not export it as a function");
      continue;
    }
    const unsupported = fn.params.filter((p) => p.kind === "other");
    if (unsupported.length > 0 && generator === undefined) {
      skip(`parameter ${unsupported.map((p) => `\`${p.name}: ${p.type}\``).join(", ")} needs a generator (--gen)`);
      continue;
    }
    let pres: Compiled[];
    let posts: Compiled[];
    try {
      pres = fn.pre.map((text) => compile(text, fn.params));
      posts = fn.post.map((text) => compile(text, fn.params));
    } catch (error) {
      skip(`a spec is not evaluable as JavaScript: ${error instanceof Error ? error.message : String(error)}`);
      continue;
    }

    const maxAttempts = options.count * 100;
    while (report.satisfied < options.count && report.generated < maxAttempts) {
      const args = generator?.(fn.name, rng) ?? builtinArgs(fn, rng);
      report.generated += 1;
      let satisfied = true;
      for (const pre of pres) {
        try {
          if (!pre(scope, args, undefined)) satisfied = false;
        } catch {
          report.preErrors += 1;
          satisfied = false;
        }
        if (!satisfied) break;
      }
      if (!satisfied) continue;
      report.satisfied += 1;

      let result: unknown;
      try {
        result = (impl as (...a: unknown[]) => unknown)(...args);
      } catch (error) {
        if (isResourceError(error)) report.resourceThrows += 1;
        else report.findings.push({ kind: "unexpected-throw", args: describe(args), error: String(error).split("\n")[0] });
        continue;
      }
      if (!inModel(fn.returnKind, result)) {
        report.findings.push({ kind: "range", spec: `result is a safe-integer ${fn.returnType}`, args: describe(args), result: describe(result) });
      }
      fn.post.forEach((text, index) => {
        try {
          if (!posts[index]!(scope, args, result)) {
            report.findings.push({ kind: "post", spec: text, args: describe(args), result: describe(result) });
          }
        } catch (error) {
          report.findings.push({ kind: "post-error", spec: text, args: describe(args), result: describe(result), error: String(error) });
        }
      });
    }
    reports.push(report);

    const posted = fn.post.length === 0 ? " (no post tags: checked for throws and the result type only)" : "";
    console.log(
      `  ${fn.name}: ${report.satisfied}/${report.generated} generated input(s) satisfied the pre tags` +
        `${report.preErrors > 0 ? ` (${report.preErrors} pre evaluation error(s))` : ""}; ` +
        `${report.findings.length} finding(s), ${report.resourceThrows} stack-overflow throw(s)${posted}`,
    );
    if (report.satisfied === 0) console.log(`    WARNING: no generated input satisfied the pre tags; nothing was checked`);
    for (const finding of report.findings.slice(0, MAX_REPORTED)) {
      const detail = finding.error === undefined ? "" : ` (${finding.error})`;
      const spec = finding.spec === undefined ? "" : ` \`${finding.spec}\``;
      const result = finding.result === undefined ? "" : ` -> result ${finding.result}`;
      console.log(`    ${finding.kind.toUpperCase()}${spec}: args (${finding.args.replace(/^\[|\]$/g, "")})${result}${detail}`);
    }
    if (report.findings.length > MAX_REPORTED) console.log(`    … ${report.findings.length - MAX_REPORTED} more`);
  }

  if (options.json !== "") {
    writeFileSync(options.json, `${JSON.stringify({ file: options.file, mode, seed: options.seed, count: options.count, reports }, null, 2)}\n`);
  }
  const tested = reports.filter((r) => r.status === "tested" && r.satisfied > 0);
  const findings = reports.reduce((sum, r) => sum + r.findings.length, 0);
  if (findings > 0) {
    console.log(`result: VIOLATIONS (${findings} finding(s))`);
    return 1;
  }
  if (tested.length === 0) {
    console.log(`result: NOTHING TESTED (${functions.length} annotated exported function(s) found)`);
    return 2;
  }
  console.log(`result: OK (${tested.length} function(s) tested, no finding)`);
  return 0;
}

process.exit(await main());
