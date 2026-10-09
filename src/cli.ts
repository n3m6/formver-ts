/**
 * `bun run verify [paths…] [--lenient]` (specification 4.4, milestone 8).
 *
 * Verifies the given files or directories with the same driver the plugin uses, prints every
 * diagnostic and a summary table, and exits non-zero on failure.  It does **not** inject or
 * run anything: injection is the plugin's job.
 *
 * Exit codes: `0` everything verified, `1` a verification failure, `2` a usage error.
 *
 * Modes: strict by default (every function must be kernel-certified), `--lenient` accepts
 * `smt-only` obligations and uncertified imported functions as warnings.  If `libz3` is
 * missing, strict mode errors out; lenient mode warns once and treats every obligation as
 * needing a runtime check (the "no solver" rule of section 4.4).
 */
import { existsSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import { formatDiagnostic, formatDiagnostics, type Diagnostic, type DiagnosticKind } from "./diagnostics";
import { contentHash } from "./extract/specs";
import { verify, type VerifyResult } from "./verify";
import * as z3 from "./vc/z3";

const USAGE = "usage: bun run verify [paths…] [--lenient]";

/** Obligation kinds: failures a runtime check can still catch, so "no solver" downgrades them. */
const OBLIGATION_KINDS: ReadonlySet<DiagnosticKind> = new Set<DiagnosticKind>([
  "pre-call",
  "post",
  "index",
  "slice",
  "append-length",
  "range",
  "measure-nonneg",
  "measure-decrease",
  "invariant-init",
  "invariant-preserve",
]);

interface CliOptions {
  readonly paths: readonly string[];
  readonly lenient: boolean;
}

export interface FileSummary {
  readonly file: string;
  readonly certified: number;
  readonly smtOnly: number;
  readonly failed: number;
  readonly rejected: number;
  readonly axioms: number;
}

/** Parse `[paths…] [--lenient]`; throws a usage message for anything else. */
export function parseArgs(argv: readonly string[]): CliOptions {
  const paths: string[] = [];
  let lenient = false;
  for (const argument of argv) {
    if (argument === "--lenient") lenient = true;
    else if (argument === "--help" || argument === "-h") throw new Error(USAGE);
    else if (argument.startsWith("-")) throw new Error(`unknown option \`${argument}\`\n${USAGE}`);
    else paths.push(argument);
  }
  return { paths: paths.length === 0 ? ["examples/pass"] : paths, lenient };
}

/** True for `--help`/`-h`: print the usage and exit 0 instead of treating it as an error. */
function helpRequested(argv: readonly string[]): boolean {
  return argv.includes("--help") || argv.includes("-h");
}

/** The `.ts`/`.mts` files of a path: the file itself, or every file under a directory. */
export function collectFiles(target: string): string[] {
  if (!existsSync(target)) throw new Error(`no such file or directory: ${target}`);
  if (statSync(target).isFile()) return /\.(ts|mts)$/.test(target) ? [target] : [];
  const glob = new Bun.Glob("**/*.{ts,mts}");
  return [...glob.scanSync({ cwd: target, absolute: false })]
    .filter((relativePath) => !skippedPath(relativePath))
    .sort()
    .map((relativePath) => join(target, relativePath));
}

function skippedPath(relativePath: string): boolean {
  return relativePath
    .split("/")
    .some((segment) => segment === "node_modules" || (segment.startsWith(".") && segment.length > 1));
}

function span1(file: string) {
  return { file, line: 1, col: 1, offset: 0 };
}

/** Run the CLI; returns the process exit code. */
export function run(argv: readonly string[]): number {
  if (helpRequested(argv)) {
    console.log(USAGE);
    return 0;
  }
  let options: CliOptions;
  try {
    options = parseArgs(argv);
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    return 2;
  }
  const solverAvailable = z3.isAvailable();
  if (!solverAvailable) {
    const reason = z3.unavailableReason() ?? "the Z3 shared library could not be loaded";
    if (!options.lenient) {
      console.error(`error: ${reason}`);
      console.error("strict mode needs Z3; re-run with `--lenient` to inject runtime checks instead.");
      return 1;
    }
    console.warn(`warning: ${reason}`);
    console.warn("warning: no SMT solver is available; every obligation will be runtime-checked (lenient mode).");
  }

  let files: string[];
  try {
    files = options.paths.flatMap(collectFiles);
  } catch (error) {
    console.error(error instanceof Error ? error.message : String(error));
    return 1;
  }
  if (files.length === 0) {
    console.error("error: no .ts or .mts files to verify");
    return 1;
  }

  const summaries: FileSummary[] = [];
  const seen = new Set<string>();
  let failure = false;
  for (const file of files) {
    const absolute = resolve(file);
    if (seen.has(absolute)) continue;
    seen.add(absolute);
    const result = verify(file, readFileSync(file, "utf8"), {
      strict: !options.lenient,
      verifyImports: true,
      solver: solverAvailable,
    });
    // Without a solver, lenient mode warns once (above) and runtime-checks every obligation:
    // the per-obligation notes would repeat the same warning once per site.
    const diagnostics =
      options.lenient && !solverAvailable
        ? result.diagnostics.filter(
            (diagnostic) => diagnostic.kind !== "uncertified" && !OBLIGATION_KINDS.has(diagnostic.kind),
          )
        : result.diagnostics;
    const extra = externalDiagnostics(result, options.lenient);
    const printed = [...diagnostics, ...extra];
    if (printed.length > 0) console.log(printed.map(formatDiagnostic).join("\n"));
    if (printed.some((diagnostic) => diagnostic.severity === "error")) failure = true;
    if (result.axioms.length > 0) {
      console.error(`${file}: error[internal]: ${result.axioms.length} axiom(s) used: ${result.axioms.join(", ")}`);
      failure = true;
    }
    if (!options.lenient && !result.ok) failure = true;
    summaries.push(summarize(file, result));
  }
  printSummary(summaries, solverAvailable);
  return failure ? 1 : 0;
}

/** The section 6.1.5 rule: every `external` must be certified in its own file under this hash. */
function externalDiagnostics(result: VerifyResult, lenient: boolean): Diagnostic[] {
  const out: Diagnostic[] = [];
  for (const external of result.externals) {
    if (external.certified !== true) {
      out.push({
        kind: "uncertified",
        severity: lenient ? "warning" : "error",
        span: span1(result.path),
        message:
          `the imported declaration \`${external.name}\` is not certified in ${external.file}` +
          `${external.certified === "unknown" ? " (its verdict is unknown)" : ""}; ` +
          `${lenient ? "its preconditions will be runtime-checked" : "strict mode requires it to be certified"}`,
      });
      continue;
    }
    let current: string;
    try {
      current = contentHash(readFileSync(external.file, "utf8"));
    } catch (error) {
      out.push({
        kind: "internal",
        severity: "error",
        span: span1(result.path),
        message: `cannot re-read ${external.file}: ${error instanceof Error ? error.message : String(error)}`,
      });
      continue;
    }
    if (current !== external.hash) {
      out.push({
        kind: "internal",
        severity: "error",
        span: span1(result.path),
        message:
          `the external declaration \`${external.name}\` was admitted from content ` +
          `${external.hash.slice(0, 12)}… but ${external.file} now hashes to ${current.slice(0, 12)}…`,
      });
    }
  }
  return out;
}

/** The per-file counts of the summary table; exported for `scripts/demo.ts`. */
export function summarize(file: string, result: Pick<VerifyResult, "functions" | "axioms">): FileSummary {
  let certified = 0;
  let smtOnly = 0;
  let failed = 0;
  let rejected = 0;
  for (const fn of result.functions) {
    if (fn.status === "certified") certified += 1;
    else if (fn.status === "smt-only") smtOnly += 1;
    else if (fn.status === "rejected") rejected += 1;
    else failed += 1;
  }
  return { file, certified, smtOnly, failed, rejected, axioms: result.axioms.length };
}

/** Print the summary table `bun run verify` ends with; exported for `scripts/demo.ts`. */
export function printSummary(summaries: readonly FileSummary[], solverAvailable: boolean): void {
  const width = Math.max(4, ...summaries.map((summary) => summary.file.length));
  const row = (file: string, values: readonly (string | number)[]): string =>
    `${file.padEnd(width)}  ${values.map((value) => String(value).padStart(9)).join("  ")}`;
  console.log("");
  console.log(row("file", ["certified", "smt-only", "failed", "rejected"]));
  for (const summary of summaries) {
    console.log(row(summary.file, [summary.certified, summary.smtOnly, summary.failed, summary.rejected]));
  }
  const total = (pick: (summary: FileSummary) => number): number =>
    summaries.reduce((sum, summary) => sum + pick(summary), 0);
  console.log(
    row("total", [total((s) => s.certified), total((s) => s.smtOnly), total((s) => s.failed), total((s) => s.rejected)]),
  );
  const axioms = total((summary) => summary.axioms);
  console.log(`axioms used: ${axioms}${axioms === 0 ? "" : " (must be 0)"}`);
  if (!solverAvailable) console.log("note: no SMT solver available; every obligation needs a runtime check");
  // A trailing separator makes the table easy to spot in a long terminal log.
  console.log(`${summaries.length} file(s) verified`);
}

if (import.meta.main) {
  process.exit(run(Bun.argv.slice(2)));
}
