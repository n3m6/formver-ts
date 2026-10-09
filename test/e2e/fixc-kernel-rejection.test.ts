/**
 * Regression (fixc 1): a term the kernel rejects is **always** reported as an `internal`
 * error and leaves the function `failed`, whatever the solver situation.
 *
 * `src/extract/elaborate.ts` runs `K.checkType` on the completed term and used to discard the
 * rejection whenever any obligation was `smt-only` — "Z3 proved it but found no certificate",
 * or "no solver is present at all" (section 4.4) — silently reporting the function as
 * `smt-only`.  A term that does not type-check is a bug in the elaborator, not a missing
 * certificate, so it must never hide behind an undischarged obligation.
 *
 * The one exception is an *incomplete* term: the placeholder `tt` an undischarged obligation
 * leaves in a proof position makes the kernel stop at that placeholder
 * (`placeholderRejection`).  The control case below pins that side of the rule: a well-typed
 * function without a solver stays `smt-only` and produces no `internal` diagnostic.
 *
 * `bad<T>(x: number): T { return x; }` is the smallest term the kernel rejects for a reason
 * of its own: the post obligation of a `T`-typed result is `Unit`, which `tt` discharges, and
 * the failure is the returned `Int` where `T` is expected.
 */
import { describe, expect, setDefaultTimeout, test } from "bun:test";
import { resolve } from "node:path";
import { verify, type VerifyResult } from "../../src/verify";

// The kernel check of a rejected term is cheap; keeping the same budget as the rest of the
// e2e suite costs nothing and keeps a slow machine from flaking.
setDefaultTimeout(60_000);

const repoRoot = resolve(import.meta.dir, "../..");

const KERNEL_REJECT = `/**
 * @pre x >= 0
 */
export function bad<T>(x: number): T {
  return x;
}
`;

/** The same shape, well-typed: the placeholder for its `Unit` post *is* a proof of it. */
const WELL_TYPED = `/**
 * @pre x >= 0
 * @post result >= 0
 */
export function good(x: number): number {
  return x;
}
`;

function run(source: string, options: Parameters<typeof verify>[2] = {}): VerifyResult {
  return verify(resolve(repoRoot, "test/e2e/fixtures/fixc-kernel-rejection.ts"), source, options);
}

describe("a kernel-rejected term is never downgraded", () => {
  for (const solver of [true, false]) {
    test(`solver: ${solver} — the function is failed with an error[internal]`, () => {
      const result = run(KERNEL_REJECT, { solver });
      const bad = result.functions.find((fn) => fn.name === "bad");
      expect(bad).toBeDefined();
      expect(bad!.status).toBe("failed");
      expect(bad!.certified).toBe(false);
      expect(result.ok).toBe(false);

      const internal = result.diagnostics.filter((d) => d.kind === "internal");
      expect(internal.length).toBe(1);
      expect(internal[0]!.severity).toBe("error");
      // Located at the function's name (`export function bad<T>…` is line 4, `bad` column 17).
      expect([internal[0]!.span.line, internal[0]!.span.col]).toEqual([4, 17]);
      expect(internal[0]!.message).toContain("the kernel rejected the elaborated term of `bad`");
    });
  }

  test("without a solver the obligation warning is still reported next to the error", () => {
    const result = run(KERNEL_REJECT, { solver: false });
    const warning = result.diagnostics.find((d) => d.kind === "uncertified");
    expect(warning).toBeDefined();
    expect(warning!.severity).toBe("warning");
    expect(warning!.message).toContain("no SMT solver is available");
    // Both diagnostics are about the same function, and the error is the one that decides.
    expect(result.functions[0]!.status).toBe("failed");
  });

  test("without a solver the function is not admitted as `def` either", () => {
    const result = run(KERNEL_REJECT, { solver: false });
    const declared = result.env.decls.get("bad");
    // Lenient mode admits the *spec* as an `external` declaration so callers can be
    // elaborated; it is never a `def` the kernel accepted.
    expect(declared?.kind).toBe("external");
    expect(result.axioms).toEqual([]);
  });
});

describe("the control: an undischarged obligation is not an error", () => {
  test("a well-typed function without a solver is `smt-only`, with a warning and no error", () => {
    const result = run(WELL_TYPED, { solver: false });
    expect(result.functions[0]!.status).toBe("smt-only");
    expect(result.functions[0]!.certified).toBe(false);
    expect(result.diagnostics.some((d) => d.kind === "internal")).toBe(false);
    const warnings = result.diagnostics.filter((d) => d.kind === "uncertified" && d.severity === "warning");
    expect(warnings.length).toBeGreaterThan(0);
    expect(warnings[0]!.message).toContain("no SMT solver is available");
    // Lenient mode: not discharged, but a runtime check will be injected, so the file is ok.
    expect(result.ok).toBe(true);
  });

  test("with a solver the same function is certified", () => {
    const result = run(WELL_TYPED, { solver: true });
    expect(result.functions[0]!.status).toBe("certified");
    expect(result.axioms).toEqual([]);
    expect(result.ok).toBe(true);
  });
});
