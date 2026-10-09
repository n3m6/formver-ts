/**
 * Shared fixtures for the milestone-6 tests (`src/vc/`).
 *
 * Every obligation in these tests is built the way the elaborator will build it: terms in
 * an ambient context of `depth` binders, with each binder's *domain* written in the context
 * of the binders before it (that is the kernel's `Ctx` convention, and what
 * `src/extract/fragment.ts` stores on a `Binder`).
 *
 * `closeProof` turns an obligation plus the proof `certify` returned into a closed term and
 * a closed type, which is how the tests exercise `K.checkType` — exactly what the kernel
 * does when it checks the elaborated function.
 */
import { test } from "bun:test";
import * as K from "../../src/kernel/index";
import type { Span } from "../../src/diagnostics";
import * as O from "../../src/vc/obligations";
import * as Z from "../../src/vc/z3";

export const env: K.Env = K.emptyEnv();

export function span(line = 1, col = 1): Span {
  return { file: "test/vc/example.ts", line, col, offset: 0, endOffset: 0 };
}

/** True when `.z3/libz3.so` (or `DEP_VERIFY_LIBZ3`) loads. */
export const z3Available: boolean = Z.isAvailable();

if (!z3Available) {
  console.warn(
    `[test/vc] Z3 is unavailable (${Z.unavailableReason() ?? "unknown reason"}); ` +
      `the obligation tests are skipped. Run \`bun run setup\` to download Z3 5.1.0.`,
  );
}

/** `test` when Z3 loads, `test.skip` otherwise, so the suite never hard-fails without it. */
export const whenZ3: typeof test = z3Available ? test : test.skip;

/** The `atomNames` for a context of `depth` binders, by source name. */
export function names(depth: number, binderNames: readonly string[]): Record<string, string> {
  return O.contextAtomNames(depth, binderNames);
}

/**
 * Close a proof under its ambient context: `fun (x0 : A0) … => proof`, of type
 * `(x0 : A0) -> … -> goal`. The domains are already in the right (preceding) context, so
 * no shifting is needed — the ambient de Bruijn indices of `proof` and `goal` line up with
 * the new binders by construction.
 */
export function closeProof(
  domains: readonly K.Term[],
  binderNames: readonly string[],
  proof: K.Term,
  goal: K.Term,
): { readonly term: K.Term; readonly type: K.Term } {
  let term = proof;
  let type = goal;
  for (let position = domains.length - 1; position >= 0; position -= 1) {
    term = K.lam(binderNames[position]!, domains[position]!, term);
    type = K.pi(binderNames[position]!, domains[position]!, type);
  }
  return { term, type };
}

/** `K.checkType` on the closed form of `proof`; returns the raw result for assertions. */
export function checkClosed(
  domains: readonly K.Term[],
  binderNames: readonly string[],
  proof: K.Term,
  goal: K.Term,
): K.Result<void> {
  const { term, type } = closeProof(domains, binderNames, proof, goal);
  return K.checkType(env, term, type);
}

/** A `file:line:col` span for a synthetic obligation. */
export function obligation(
  id: string,
  goal: K.Term,
  hypotheses: readonly K.Term[],
  context: readonly K.Term[] | undefined,
  binderNames: readonly string[] | undefined,
  kind: string = "post",
): O.Obligation {
  return {
    id,
    kind: kind as O.Obligation["kind"],
    span: span(),
    hypotheses,
    goal,
    context,
    ...(binderNames === undefined ? {} : { atomNames: names(context?.length ?? 0, binderNames) }),
  };
}
