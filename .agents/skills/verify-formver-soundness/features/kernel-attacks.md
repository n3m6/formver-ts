# Kernel attacks

The kernel in `src/kernel/` is the only trusted component. Every `certified` verdict is a term
it type-checked. If any term of type `Empty` (false) is accepted, or conversion identifies
two different types, every verdict is suspect. These recipes attack the kernel directly
through its public API, the way an untrusted elaborator would.

## Sub-features

- `kernel-baseline`: the repo's own prove-false cases (`scripts/prove-false.ts`, demo step 7, `test/kernel/`) are all rejected for the expected reason.
- `kernel-farkas`: Farkas certificates with wrong, zero, negative or non-`Le` multipliers; per-row tightening edge cases (GCD, constants).
- `kernel-le`: `LeProof a b` with `a > b`; `Lt` encoded as `Le (a+1) b`; `Le` conversion by difference.
- `kernel-conversion`: `isConvertible` on linear forms (`x - x` against `x`, swapped `Le` arguments, `Vec A n` against `Vec A (n+1)`).
- `kernel-vec`: `get` without a bounds proof or with someone else's; `append`/`slice` length proofs; `castVec` with a bogus `Eq`.
- `kernel-fixwf`: `fixWf` with a missing or reversed decrease proof, a negative measure, or an unfolding that skips the step.
- `kernel-primitives`: the trusted lemmas (`vecBounds`, `divFloorSpec`, `divTruncSpecNonneg`, `divTruncSpecNeg`) applied outside their stated conditions.
- `kernel-universes`: `Type 0 : Type 0` and impredicativity tricks.

## How to get to it (user POV)

- A user never calls the kernel; they trust it through `certified`. The attack harness
  stands in for a buggy or malicious elaborator.

## Driving it with the soundness tools

Preconditions:

- The baseline preconditions in `README.md` hold, and `$RUN` exists.
- You have read `docs/KERNEL_NOTES.md` (the rules and what each primitive trusts) and `scripts/prove-false.ts` (the term-builder idioms).

- **Baseline.** Run `$SK/capture.sh "$RUN" kernel-attacks.kernel-baseline.tests -- bun test test/kernel`, which reports `0 fail`. Then run `$SK/capture.sh "$RUN" kernel-attacks.kernel-baseline.demo -- env DEP_VERIFY_NO_CACHE=1 bun run demo`. Its step 7 lists every prove-false case as `rejected`, and the run ends with `demo complete: all 7 steps behaved as specified`.
- **Starter attacks.** Run `cp $SS/attacks.example.ts "$RUN/scratch/attacks.ts"`, then `$SK/capture.sh "$RUN" kernel-attacks.starter -- bun $SS/kernel-attack.ts "$RUN/scratch/attacks.ts"`. The result is `8 attack(s), 0 problem(s)`: three `[control]` lines are `accepted` or `convertible`, and five attacks are `rejected: <reason>` or `not convertible`.
- **New attacks.** Add entries to `$RUN/scratch/attacks.ts` for the sub-feature you are probing, each with `expect: "reject"`, and pair each family with at least one `expect: "accept"` control built the same way. Re-run with label `kernel-attacks.<sub-feature>`. Every line must be `ok`. An `ACCEPTED` line is a kernel soundness bug: keep the attack file, which cleanup archives to `evidence/inputs/attacks.ts`, and report the term. A `CONTROL-FAILED` line means the attack file is wrong, not the kernel.
- **Promote real findings.** An attack that exposes a bug (or guards a subtle rule) belongs in `scripts/prove-false.ts` and `test/kernel/`, but adding it is a code change for the user to approve, not part of verification.

## Gotchas

- `kernel-attack.ts` must import the kernel only through `src/kernel/index.ts`, the API the
  elaborator uses. Reaching into internal modules tests something users never hit.
- The attack file receives the kernel as its argument (`export default (K) => [...]`), so
  copying it into scratch needs no import-path changes. Its `import type` lines are erased
  at runtime.
- `isConvertible` returns `false` for an environment the kernel did not create. Always start
  from `K.emptyEnv()`, never a hand-built object, or every conversion attack "passes".
- A rejection only counts as a defense if the reason fits the attack. A term that is rejected
  for an arity error because you mis-built it says nothing about the rule you meant to
  attack. Read the reason, and keep a control that differs only in the attacked detail.
- `LeProof a b` is checked like a Farkas certificate: a false one is rejected as
  `farkas-invalid`, not with a type mismatch.
