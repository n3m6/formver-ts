#!/usr/bin/env bun
/**
 * Write single-change mutants of an annotated source file, so you can check that the
 * verifier stops certifying a program once it no longer meets its spec.
 *
 * Usage: bun mutate.ts <file.ts> <out-dir> [--max N]
 *
 * Each mutant is <out-dir>/<NNN>/<basename> next to copies of the file's sibling .ts files (so
 * relative imports still resolve), plus <out-dir>/<NNN>/MUTATION.txt. One line per mutant goes
 * to stdout: "<NNN>\t<line>\t<operator>\t<before> => <after>".
 *
 * Code lines get operator swaps (comparison, equality, + and -, && and ||, floor and trunc,
 * max and min) and integer literals n±1. Spec tag lines get the same swaps; precondition,
 * invariant and termination-measure tags can also be dropped, as can single conjuncts of
 * precondition and invariant tags. With more than --max mutants (default 60), an even spread
 * is kept.
 */
import { copyFileSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { basename, dirname, join, resolve } from "node:path";

interface Mutant {
  readonly line: number;
  readonly operator: string;
  readonly before: string;
  readonly after: string;
  readonly source: string;
}

const SWAPS: readonly (readonly [string, RegExp, string])[] = [
  ["<= to <", / <= /g, " < "],
  ["< to <=", / < /g, " <= "],
  [">= to >", / >= /g, " > "],
  ["> to >=", / > /g, " >= "],
  ["=== to !==", / === /g, " !== "],
  ["!== to ===", / !== /g, " === "],
  ["+ to -", / \+ /g, " - "],
  ["- to +", / - /g, " + "],
  ["&& to ||", / && /g, " || "],
  ["floor to trunc", /Math\.floor\(/g, "Math.trunc("],
  ["trunc to floor", /Math\.trunc\(/g, "Math.floor("],
  ["max to min", /Math\.max\(/g, "Math.min("],
  ["min to max", /Math\.min\(/g, "Math.max("],
];
const LITERAL = /(?<![\w.$])\d+(?![\w.])/g;
const TAG = /@(pre|post|invariant|decreases)(\s+)/;

const [fileArg, outArg, ...rest] = process.argv.slice(2);
if (fileArg === undefined || outArg === undefined) {
  console.error("usage: bun mutate.ts <file.ts> <out-dir> [--max N]");
  process.exit(2);
}
let max = 60;
for (let i = 0; i < rest.length; i += 1) {
  if (rest[i] === "--max") max = Number(rest[++i]);
}
const file = resolve(fileArg);
const outDir = resolve(outArg);
const lines = readFileSync(file, "utf8").split("\n");

/** The part of a line that may be mutated: [start, end) offsets, plus the tag on spec lines. */
interface Region {
  readonly start: number;
  readonly end: number;
  readonly tag?: string;
}

function regions(): (Region | undefined)[] {
  let inComment = false;
  return lines.map((line) => {
    const trimmed = line.trim();
    const opens = !inComment && trimmed.startsWith("/*");
    const commentLine = inComment || opens;
    if (commentLine) {
      const closes = line.indexOf("*/", opens ? line.indexOf("/*") + 2 : 0);
      inComment = closes < 0;
      const tag = TAG.exec(line);
      if (tag === null) return undefined;
      const start = tag.index + tag[0].length;
      return { start, end: closes < 0 ? line.length : closes, tag: tag[1] };
    }
    if (
      trimmed === "" ||
      /^(import|export\s+type|type|export\s+function|function|\/\/|\||\})/.test(trimmed)
    ) {
      return undefined;
    }
    const comment = line.indexOf("//");
    return { start: 0, end: comment < 0 ? line.length : comment };
  });
}

function splitConjuncts(text: string): string[] {
  const parts: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i]!;
    if (ch === "(") depth += 1;
    else if (ch === ")") depth -= 1;
    else if (depth === 0 && text.startsWith(" && ", i)) {
      parts.push(text.slice(start, i));
      start = i + 4;
      i += 3;
    }
  }
  parts.push(text.slice(start));
  return parts;
}

const mutants: Mutant[] = [];
const seen = new Set<string>();
function add(line: number, operator: string, after: string | undefined): void {
  const replaced = [...lines];
  if (after === undefined) replaced.splice(line, 1);
  else replaced[line] = after;
  const source = replaced.join("\n");
  if (seen.has(source)) return;
  seen.add(source);
  mutants.push({ line: line + 1, operator, before: lines[line]!, after: after ?? "(line removed)", source });
}

regions().forEach((region, index) => {
  if (region === undefined) return;
  const line = lines[index]!;
  const head = line.slice(0, region.start);
  const body = line.slice(region.start, region.end);
  const tail = line.slice(region.end);
  const where = region.tag === undefined ? "code" : `${region.tag} tag`;

  for (const [name, pattern, replacement] of SWAPS) {
    for (const match of body.matchAll(pattern)) {
      const mutated = body.slice(0, match.index) + replacement + body.slice(match.index! + match[0].length);
      add(index, `${where}: ${name}`, head + mutated + tail);
    }
  }
  for (const match of body.matchAll(LITERAL)) {
    const value = BigInt(match[0]);
    for (const delta of [1n, -1n]) {
      if (value + delta < 0n) continue;
      const mutated = body.slice(0, match.index) + String(value + delta) + body.slice(match.index! + match[0].length);
      add(index, `${where}: literal ${match[0]} to ${value + delta}`, head + mutated + tail);
    }
  }
  if (region.tag === "pre" || region.tag === "invariant" || region.tag === "decreases") {
    add(index, `${where}: drop the tag`, undefined);
  }
  if (region.tag === "pre" || region.tag === "invariant") {
    const conjuncts = splitConjuncts(body.trimEnd());
    if (conjuncts.length > 1) {
      conjuncts.forEach((conjunct, drop) => {
        const kept = conjuncts.filter((_, i) => i !== drop).join(" && ");
        add(index, `${where}: drop conjunct \`${conjunct.trim()}\``, head + kept + tail);
      });
    }
  }
});

const chosen =
  mutants.length <= max
    ? mutants
    : Array.from({ length: max }, (_, i) => mutants[Math.floor((i * mutants.length) / max)]!);

const siblings = readdirSync(dirname(file)).filter((name) => /\.(ts|mts)$/.test(name) && name !== basename(file));
chosen.forEach((mutant, i) => {
  const id = String(i + 1).padStart(3, "0");
  const dir = join(outDir, id);
  mkdirSync(dir, { recursive: true });
  for (const sibling of siblings) copyFileSync(join(dirname(file), sibling), join(dir, sibling));
  writeFileSync(join(dir, basename(file)), mutant.source);
  writeFileSync(
    join(dir, "MUTATION.txt"),
    `source: ${file}\nline: ${mutant.line}\noperator: ${mutant.operator}\nbefore: ${mutant.before}\nafter: ${mutant.after}\n`,
  );
  console.log(`${id}\t${mutant.line}\t${mutant.operator}\t${mutant.before.trim()} => ${mutant.after.trim()}`);
});
console.error(`mutate: ${chosen.length} of ${mutants.length} mutant(s) written to ${outDir}`);
