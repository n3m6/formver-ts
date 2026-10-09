#!/usr/bin/env bun
/**
 * `bun run demo` — the guided walkthrough of specification section 10.
 *
 * Seven steps, in order:
 *
 *   1. `examples/pass/clamp.ts`: the source, its verdict, and the obligation/certificate counts
 *   2. `examples/fail/clampNoPre.ts`: the `error[post]` diagnostic and its counterexample
 *   3. `binarySearch`, `sumTo`, `shape` and `useClamp`: all certified, plus the summary table
 *   4. `examples/fail/`: every diagnostic kind the verifier reports
 *   5. `examples/runtime/main.ts` under the preload plugin: `PreconditionError`, exact line
 *   6. `Bun.build` of `examples/pass` with `NODE_ENV=production`: what stays, what is stripped
 *   7. the kernel's prove-`false` cases: each attempt to prove `false`, and its rejection reason
 *
 * It is **non-interactive** and reads only committed files: everything it prints is computed
 * from the real verifier, the real plugin and the real kernel (counts, diagnostics, build
 * output, rejection reasons).  A step that does not behave as specified makes the demo exit
 * non-zero.  Steps 2 and 4 *expect* failures: a deliberately broken example must be reported,
 * so "the verifier said no" is the passing outcome there.
 */
import { readFileSync } from "node:fs";
import { relative, resolve } from "node:path";
import { verifyCached, type CachedVerifyReport } from "../src/cache";
import { printSummary, summarize, type FileSummary } from "../src/cli";
import { formatDiagnostic } from "../src/diagnostics";
import { depVerifyPlugin, REPO_ROOT } from "../src/plugin";
import * as z3 from "../src/vc/z3";
import { proveFalseCases, runProveFalseCase } from "./prove-false";

// Everything below uses repository-relative paths (`examples/pass/clamp.ts`), exactly like
// `bun run verify`, so the diagnostics and the summary table read the way a user sees them.
process.chdir(REPO_ROOT);

const RULE = "-".repeat(74);
const SOLVER = z3.isAvailable();

/** One `bun run demo` failure: an expectation of section 10 that did not hold. */
let failures = 0;

function heading(index: number, title: string): void {
  console.log(`\n${index}. ${title}`);
  console.log(RULE);
}

function ok(message: string): void {
  console.log(`  [ok] ${message}`);
}

function fail(message: string): void {
  failures += 1;
  console.log(`  [FAIL] ${message}`);
}

function check(condition: boolean, success: string, failure: string): void {
  if (condition) ok(success);
  else fail(failure);
}

function read(path: string): string {
  return readFileSync(resolve(REPO_ROOT, path), "utf8");
}

/** Print a source file with line numbers, so diagnostics can be read against it. */
function showSource(path: string): void {
  const lines = read(path).replace(/\n$/, "").split("\n");
  const width = String(lines.length).length;
  lines.forEach((line, index) => console.log(`  ${String(index + 1).padStart(width)} | ${line}`));
}

/** Verify one file through the same driver the plugin and the CLI use (with the cache). */
function verifyFile(path: string): CachedVerifyReport {
  return verifyCached(path, read(path), { strict: true, solver: SOLVER });
}

function statuses(result: CachedVerifyReport): string {
  return result.functions.map((fn) => `${fn.name} = ${fn.status}`).join(", ");
}

function milliseconds(started: number): string {
  return `${Date.now() - started} ms`;
}

/** The `.ts` files of a directory, repository-relative and sorted. */
function filesIn(directory: string): string[] {
  const glob = new Bun.Glob("*.ts");
  return [...glob.scanSync({ cwd: resolve(REPO_ROOT, directory) })].sort().map((file) => `${directory}/${file}`);
}

// ---------------------------------------------------------------------------
// 0. Preamble
// ---------------------------------------------------------------------------

console.log("formver-ts demo — build-time dependent-type verification for a pure TypeScript subset");
console.log(`bun ${Bun.version}, ${z3.version() ?? "Z3 unavailable"}`);
console.log(`repository: ${REPO_ROOT}`);
if (!SOLVER) {
  console.error(`\nerror: Z3 is not available: ${z3.unavailableReason() ?? "unknown reason"}`);
  console.error("run `bun run setup` first (Linux x64), or point DEP_VERIFY_LIBZ3 at a libz3 shared library.");
  process.exit(1);
}

// ---------------------------------------------------------------------------
// 1. A certified function
// ---------------------------------------------------------------------------

heading(1, "`clamp`: a spec, a kernel-certified verdict, and the proof counts");
showSource("examples/pass/clamp.ts");
{
  const started = Date.now();
  const result = verifyFile("examples/pass/clamp.ts");
  const obligations = result.functions.flatMap((fn) => fn.obligations);
  const certificates = obligations.filter((obligation) => obligation.status === "certified");
  const smtOnly = obligations.filter((obligation) => obligation.status === "smt-only");
  const failed = obligations.filter((obligation) => obligation.status === "failed");
  console.log("");
  console.log(`  verdict: ${statuses(result)} (${milliseconds(started)}${result.cached ? ", cache hit" : ""})`);
  console.log(`  certified by kernel, ${result.axioms.length} axioms`);
  console.log(
    `  ${obligations.length} obligations, ${certificates.length} certificates` +
      ` (smt-only ${smtOnly.length}, failed ${failed.length})`,
  );
  check(result.ok, "the file verifies in strict mode", "strict verification failed");
  check(
    result.functions.every((fn) => fn.status === "certified"),
    "every function is kernel-certified",
    `not every function is certified: ${statuses(result)}`,
  );
  check(result.axioms.length === 0, "no axioms were used", `axioms used: ${result.axioms.join(", ")}`);
  check(
    obligations.length > 0 && certificates.length === obligations.length,
    `each of the ${obligations.length} obligations came with a kernel-checked certificate`,
    `${obligations.length - certificates.length} obligation(s) had no certificate`,
  );
}

// ---------------------------------------------------------------------------
// 2. A postcondition that does not hold
// ---------------------------------------------------------------------------

heading(2, "`clampNoPre`: the same postcondition without its precondition");
showSource("examples/fail/clampNoPre.ts");
{
  const result = verifyFile("examples/fail/clampNoPre.ts");
  console.log("");
  for (const diagnostic of result.diagnostics) {
    console.log(
      formatDiagnostic(diagnostic)
        .split("\n")
        .map((line) => `  ${line}`)
        .join("\n"),
    );
  }
  const withCounterexample = result.diagnostics.filter(
    (diagnostic) => diagnostic.counterexample !== undefined && Object.keys(diagnostic.counterexample).length > 0,
  );
  console.log("");
  check(result.ok === false, "the file does not verify", "the file unexpectedly verified");
  check(
    result.diagnostics.some((diagnostic) => diagnostic.kind === "post"),
    "the failure is reported as an `error[post]` at the return that can break it",
    "no `post` diagnostic was reported",
  );
  check(
    withCounterexample.length > 0,
    `${withCounterexample.length} diagnostic(s) carry a counterexample from Z3`,
    "no diagnostic carried a counterexample",
  );
}

// ---------------------------------------------------------------------------
// 3. Loops, recursion, tagged unions and a cross-file call
// ---------------------------------------------------------------------------

heading(3, "`binarySearch`, `sumTo`, `shape`, `useClamp`: loops, recursion, unions, imports");
{
  const files = [
    "examples/pass/binarySearch.ts",
    "examples/pass/sumTo.ts",
    "examples/pass/shape.ts",
    "examples/pass/useClamp.ts",
  ];
  const summaries: FileSummary[] = [];
  for (const file of files) {
    console.log(`  verifying ${file} ...`);
    const started = Date.now();
    const result = verifyFile(file);
    summaries.push(summarize(file, result));
    console.log(`    ${statuses(result)} (${milliseconds(started)}${result.cached ? ", cache hit" : ""})`);
    check(
      result.ok && result.functions.every((fn) => fn.status === "certified"),
      `${file} is certified`,
      `${file} did not certify: ${statuses(result)}`,
    );
    for (const external of result.externals) {
      console.log(
        `    note: \`${external.name}\` is imported from ${relative(REPO_ROOT, external.file)};` +
          ` its spec was read by parsing, never by importing (hash ${external.hash.slice(0, 12)}…)`,
      );
    }
  }
  console.log("\n  the same summary table `bun run verify` prints:");
  printSummary(summaries, SOLVER);
}

// ---------------------------------------------------------------------------
// 4. Every diagnostic kind
// ---------------------------------------------------------------------------

heading(4, "`examples/fail/`: one located diagnostic per rejected construct");
{
  const expectedKinds = ["post", "index", "range", "measure-decrease", "fragment"] as const;
  const kinds = new Set<string>();
  for (const file of filesIn("examples/fail")) {
    const result = verifyFile(file);
    console.log(`\n  ${file}  (${statuses(result)})`);
    for (const diagnostic of result.diagnostics) {
      for (const line of formatDiagnostic(diagnostic).split("\n")) console.log(`    ${line}`);
      kinds.add(diagnostic.kind);
    }
    check(result.ok === false, `${file} is rejected`, `${file} unexpectedly verified`);
  }
  console.log("");
  for (const kind of expectedKinds) {
    check(kinds.has(kind), `the run produced an \`error[${kind}]\``, `no \`${kind}\` diagnostic was produced`);
  }
}

// ---------------------------------------------------------------------------
// 5. Runtime checks under the preload plugin
// ---------------------------------------------------------------------------

heading(5, "runtime checks: `examples/runtime/main.ts` under the preload plugin");
{
  const main = "examples/runtime/main.ts";
  console.log(`  $ bun run ${main}`);
  const child = Bun.spawnSync({
    cmd: ["bun", "run", main],
    cwd: REPO_ROOT,
    env: { ...process.env, NODE_ENV: "development", DEP_VERIFY_STRICT: "0" },
    stdout: "pipe",
    stderr: "pipe",
  });
  const exitCode = child.exitCode ?? -1;
  const stdout = child.stdout.toString().trimEnd();
  const stderr = child.stderr.toString().trimEnd();
  console.log(`  exit code ${exitCode}`);
  console.log("  stdout:");
  for (const line of stdout.split("\n")) console.log(`    ${line}`);
  console.log("  stderr:");
  const stderrLines = stderr.split("\n");
  for (const line of stderrLines.slice(0, 40)) console.log(`    ${line}`);
  if (stderrLines.length > 40) console.log(`    … (${stderrLines.length - 40} more lines)`);

  // The line the precondition check sits on is computed from the source, not hard-coded.
  const safeGet = read("examples/pass/safeGet.ts").split("\n");
  const functionLine = safeGet.findIndex((line) => line.includes("export function safeGet")) + 1;
  const frame = /^\s*at .*safeGet\.ts:(\d+):(\d+)/m.exec(stderr);
  console.log("");
  check(exitCode !== 0, "the out-of-bounds call aborts the process", "the process exited 0");
  check(
    stderr.includes("PreconditionError") && stderr.includes("0 <= i && i < a.length"),
    "the injected `@pre` check raised `PreconditionError` with the spec text",
    "no `PreconditionError` for `0 <= i && i < a.length` was found in stderr",
  );
  check(
    frame !== null && Number(frame[1]) === functionLine,
    `the top stack frame is safeGet.ts:${functionLine} — the function's own line, because injection adds no lines` +
      (frame === null ? "" : ` (found :${frame[1]}:${frame[2]})`),
    `expected a stack frame at safeGet.ts:${functionLine}, found ${frame === null ? "none" : `:${frame[1]}`}`,
  );
}

// ---------------------------------------------------------------------------
// 6. Production builds
// ---------------------------------------------------------------------------

/** What a build must do with the checks whose marker is counted below (section 6.6). */
const BUILD_MARKERS: readonly { marker: string; expectation: "kept" | "stripped"; note: string }[] = [
  { marker: "guardInt(", expectation: "kept", note: "boundary guard, exported `number` parameter" },
  { marker: "guardIntArray(", expectation: "kept", note: "boundary guard, exported `readonly number[]` (every element)" },
  { marker: "guardArray(", expectation: "kept", note: "boundary guard, exported array parameter" },
  { marker: "new PreconditionError(\"", expectation: "kept", note: "`@pre` check of an exported function" },
  { marker: "new PostconditionError(\"", expectation: "stripped", note: "certified `@post` check" },
  { marker: "checkIndex(", expectation: "stripped", note: "certified `index` obligation" },
  { marker: "checkSlice(", expectation: "stripped", note: "certified `slice` obligation" },
  { marker: "checkLength(", expectation: "stripped", note: "certified `append-length` obligation" },
  { marker: "checkRange(", expectation: "stripped", note: "certified `range` obligation" },
  { marker: "checkPre(", expectation: "stripped", note: "certified `pre-call` obligation" },
  { marker: "checkInvariant(", expectation: "stripped", note: "certified loop invariant" },
  { marker: "checkMeasure(", expectation: "stripped", note: "certified termination measure" },
  { marker: "checkMeasureDecrease(", expectation: "stripped", note: "certified strict-decrease monitor" },
];

function countOccurrences(text: string, marker: string): number {
  return text.split(marker).length - 1;
}

function lineContaining(text: string, needle: string): string | undefined {
  return text.split("\n").find((line) => line.includes(needle))?.trim();
}

/** `Bun.build` with the plugin, with `NODE_ENV` set for the duration of the build. */
async function buildPassExamples(nodeEnv: string): Promise<{ success: boolean; output: string; files: number }> {
  const previous = process.env["NODE_ENV"];
  process.env["NODE_ENV"] = nodeEnv;
  try {
    const result = await Bun.build({
      entrypoints: filesIn("examples/pass").map((file) => resolve(REPO_ROOT, file)),
      plugins: [depVerifyPlugin],
      target: "bun",
    });
    for (const log of result.logs) console.log(`    build log: ${log.message}`);
    const output = (await Promise.all(result.outputs.map((artifact) => artifact.text()))).join("\n");
    return { success: result.success, output, files: result.outputs.length };
  } finally {
    if (previous === undefined) delete process.env["NODE_ENV"];
    else process.env["NODE_ENV"] = previous;
  }
}

heading(6, "`Bun.build` with `NODE_ENV=production`: preconditions stay, certified checks go");
{
  console.log("  building examples/pass twice with the plugin (development, then production) ...");
  const started = Date.now();
  const development = await buildPassExamples("development");
  const production = await buildPassExamples("production");
  console.log(
    `  build succeeded: ${development.files} and ${production.files} output file(s) in ${milliseconds(started)}`,
  );
  check(
    development.success && production.success,
    "both builds succeeded",
    "a build failed; see the build logs above",
  );
  console.log("\n  occurrences of each injected check in the bundled output:");
  console.log(
    `    ${"check".padEnd(30)}${"development".padStart(12)}${"production".padStart(12)}   expectation`,
  );
  for (const { marker, expectation, note } of BUILD_MARKERS) {
    const dev = countOccurrences(development.output, marker);
    const prod = countOccurrences(production.output, marker);
    console.log(
      `    ${marker.padEnd(30)}${String(dev).padStart(12)}${String(prod).padStart(12)}   ` +
        `${expectation} — ${note}`,
    );
    check(
      expectation === "kept" ? prod === dev && dev > 0 : prod === 0,
      `${marker} ${expectation}`,
      `${marker} should have been ${expectation}: ${dev} in development, ${prod} in production`,
    );
  }
  const clampGuard = lineContaining(production.output, 'guardInt("clamp"');
  const clampPre = lineContaining(production.output, 'new PreconditionError("clamp"');
  const clampPost = lineContaining(development.output, 'new PostconditionError("clamp"');
  console.log("\n  the production output, verbatim:");
  for (const line of [clampGuard, clampPre]) {
    if (line !== undefined) console.log(`    ${line.slice(0, 110)}${line.length > 110 ? "…" : ""}`);
  }
  console.log("  and the development build's clamp postcondition check, gone from production:");
  if (clampPost !== undefined) console.log(`    ${clampPost.slice(0, 110)}${clampPost.length > 110 ? "…" : ""}`);
}

// ---------------------------------------------------------------------------
// 7. The kernel's prove-`false` cases
// ---------------------------------------------------------------------------

heading(7, "the kernel's prove-`false` cases: every attempt is rejected, with a reason");
{
  console.log("  (the same scenarios `test/kernel/soundness3.test.ts` asserts)\n");
  for (const entry of proveFalseCases) {
    const outcome = runProveFalseCase(entry);
    const rejected = outcome.rejection === entry.expected;
    const label = outcome.rejection === "not-convertible" ? "conversion refuses" : `error[${outcome.rejection}]`;
    console.log(`  ${rejected ? "rejected" : "ACCEPTED"}  ${entry.name}`);
    console.log(`            -> ${label}${rejected ? "" : ` (expected ${entry.expected})`}`);
    if (outcome.message !== undefined) {
      const message = outcome.message.length > 108 ? `${outcome.message.slice(0, 108)}…` : outcome.message;
      console.log(`               ${message}`);
    }
    check(rejected, `rejected for the expected reason (\`${entry.expected}\`)`, `the kernel answered \`${outcome.rejection}\``);
  }
}

// ---------------------------------------------------------------------------
// Result
// ---------------------------------------------------------------------------

console.log(`\n${RULE}`);
if (failures === 0) {
  console.log("demo complete: all 7 steps behaved as specified");
} else {
  console.log(`demo FAILED: ${failures} check(s) did not hold`);
  process.exitCode = 1;
}
