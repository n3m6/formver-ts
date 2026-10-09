#!/usr/bin/env bun
/**
 * Run hand-written attacks on the trusted kernel (src/kernel/) and report what it accepts.
 *
 * Usage: bun .agents/skills/verify-formver-soundness/scripts/kernel-attack.ts <attacks.ts>
 *
 * <attacks.ts> default-exports `(K) => Attack[]`, where K is the kernel's public API
 * (src/kernel/index.ts) and an Attack is
 *   { name: string; expect: "reject" | "accept"; run: () => K.Result<unknown> | boolean }
 * A boolean is a conversion answer (true means "convertible"). Attacks expected to be rejected
 * try to prove `Empty`/false or to make conversion identify different things. Controls
 * expected to be accepted show the attack file builds terms correctly; without them, a
 * mis-built term that fails for an unrelated reason looks like a successful defense.
 *
 * Exit 1 when an attack is accepted (a kernel soundness bug), a control is rejected (fix the
 * attack file), or the kernel throws instead of returning an error.
 */
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
import * as K from "../../../../src/kernel/index";

export interface Attack {
  readonly name: string;
  readonly expect: "reject" | "accept";
  readonly run: () => K.Result<unknown, K.KernelError> | boolean;
}

const file = process.argv[2];
if (file === undefined) {
  console.error("usage: bun kernel-attack.ts <attacks.ts>");
  process.exit(2);
}
const loaded = (await import(pathToFileURL(resolve(file)).href)) as { default: (k: typeof K) => readonly Attack[] };
const attacks = loaded.default(K);

let problems = 0;
for (const attack of attacks) {
  let accepted: boolean;
  let answer: string;
  try {
    const outcome = attack.run();
    if (typeof outcome === "boolean") {
      accepted = outcome;
      answer = outcome ? "convertible" : "not convertible";
    } else if (outcome.ok) {
      accepted = true;
      answer = "accepted";
    } else {
      accepted = false;
      answer = `rejected: ${outcome.error.reason}: ${outcome.error.message}`;
    }
  } catch (error) {
    problems += 1;
    console.log(`THREW      ${attack.name}`);
    console.log(`           ${error instanceof Error ? error.stack?.split("\n").slice(0, 3).join(" | ") : String(error)}`);
    continue;
  }
  const ok = attack.expect === "accept" ? accepted : !accepted;
  if (!ok) problems += 1;
  const label = ok ? "ok" : attack.expect === "reject" ? "ACCEPTED" : "CONTROL-FAILED";
  console.log(`${label.padEnd(10)} ${attack.expect === "accept" ? "[control] " : ""}${attack.name}`);
  console.log(`           ${answer.length > 160 ? `${answer.slice(0, 160)}…` : answer}`);
}
console.log(`${attacks.length} attack(s), ${problems} problem(s)`);
process.exit(problems === 0 ? 0 : 1);
