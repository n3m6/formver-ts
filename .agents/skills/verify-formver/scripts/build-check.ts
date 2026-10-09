#!/usr/bin/env bun
/**
 * Bundle entry points with the dep-verify plugin twice, NODE_ENV=development and then
 * NODE_ENV=production, write both bundles to disk and count every injected check in each.
 *
 * Usage: bun .agents/skills/verify-formver/scripts/build-check.ts <out-dir> <entry.ts>...
 *   bun .agents/skills/verify-formver/scripts/build-check.ts "$RUN/evidence/build" examples/pass/*.ts
 *
 * Writes <out-dir>/development/, <out-dir>/production/ and <out-dir>/markers.tsv, prints the
 * marker table, and exits 1 when either build fails. Which counts are right depends on what
 * was certified; the production-build feature file states the expectations.
 */
import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, resolve, sep } from "node:path";
import { depVerifyPlugin } from "../../../../src/plugin";

const MARKERS = [
  "guardInt(",
  "guardIntArray(",
  "guardArray(",
  "guardUnion(",
  'new PreconditionError("',
  'new PostconditionError("',
  "checkIndex(",
  "checkSlice(",
  "checkLength(",
  "checkRange(",
  "checkPre(",
  "checkInvariant(",
  "checkMeasure(",
  "checkMeasureDecrease(",
  "checkCallMeasureDecrease(",
] as const;

const [outArg, ...entryArgs] = process.argv.slice(2);
if (outArg === undefined || entryArgs.length === 0) {
  console.error("usage: bun build-check.ts <out-dir> <entry.ts>...");
  process.exit(2);
}
const outDir = resolve(outArg);
const entrypoints = entryArgs.map((entry) => resolve(entry));
/** Bundles land at `<mode>/<path relative to this>`, not relative to the runtime module in `src/`. */
function commonDirectory(files: readonly string[]): string {
  let common = dirname(files[0]!).split(sep);
  for (const file of files.slice(1)) {
    const parts = dirname(file).split(sep);
    let i = 0;
    while (i < common.length && i < parts.length && common[i] === parts[i]) i += 1;
    common = common.slice(0, i);
  }
  return common.join(sep) || sep;
}
const root = commonDirectory(entrypoints);

async function build(nodeEnv: "development" | "production"): Promise<{ ok: boolean; text: string; files: number }> {
  const previous = process.env["NODE_ENV"];
  process.env["NODE_ENV"] = nodeEnv;
  try {
    const result = await Bun.build({
      entrypoints,
      plugins: [depVerifyPlugin],
      target: "bun",
      root,
      outdir: resolve(outDir, nodeEnv),
    });
    for (const log of result.logs) console.log(`[${nodeEnv}] build log: ${log.message}`);
    const text = (await Promise.all(result.outputs.map((artifact) => artifact.text()))).join("\n");
    return { ok: result.success, text, files: result.outputs.length };
  } catch (error) {
    console.log(`[${nodeEnv}] build threw: ${error instanceof Error ? error.message : String(error)}`);
    const inner = error instanceof AggregateError ? error.errors : [];
    for (const message of inner) {
      console.log(`[${nodeEnv}] ${message instanceof Error || (message && typeof message === "object" && "message" in message) ? String((message as { message: unknown }).message) : String(message)}`);
    }
    return { ok: false, text: "", files: 0 };
  } finally {
    if (previous === undefined) delete process.env["NODE_ENV"];
    else process.env["NODE_ENV"] = previous;
  }
}

mkdirSync(outDir, { recursive: true });
const started = Date.now();
const development = await build("development");
const production = await build("production");
console.log(
  `development: ${development.ok ? "ok" : "FAILED"}, ${development.files} file(s); ` +
    `production: ${production.ok ? "ok" : "FAILED"}, ${production.files} file(s); ${Date.now() - started} ms`,
);

const count = (text: string, marker: string): number => text.split(marker).length - 1;
const rows = MARKERS.map((marker) => ({
  marker,
  development: count(development.text, marker),
  production: count(production.text, marker),
}));
console.log(`${"marker".padEnd(30)}${"development".padStart(12)}${"production".padStart(12)}`);
for (const row of rows) {
  console.log(`${row.marker.padEnd(30)}${String(row.development).padStart(12)}${String(row.production).padStart(12)}`);
}
writeFileSync(
  resolve(outDir, "markers.tsv"),
  ["marker\tdevelopment\tproduction", ...rows.map((row) => `${row.marker}\t${row.development}\t${row.production}`)].join("\n") +
    "\n",
);
console.log(`bundles and markers.tsv written to ${outDir}`);
if (!development.ok || !production.ok) process.exit(1);
