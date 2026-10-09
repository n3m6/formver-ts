# Cross-module specs

A verified function may call a verified function from another file. The verifier reads the
callee's spec by parsing its file, never by importing or executing it. It uses the callee's
precondition as an obligation at the call and its postcondition as a fact after it. In strict
mode, every imported declaration must also be certified in its own file at the same content
hash.

## Sub-features

- `xmod-certified`: `examples/pass/useClamp.ts` (`percent`, calling `clamp`) certifies on its own; exit 0.
- `xmod-no-execution`: a top-level side effect in the callee's file never runs during verification.
- `xmod-uncertified-import`: calling an uncertified function fails strict mode with `error[uncertified]`; `--lenient` exits 0.
- `xmod-spec-weakened`: weakening the callee's postcondition makes the caller fail with `error[post]`.
- `xmod-pre-strengthened`: strengthening the callee's precondition makes the caller's call site fail.
- `xmod-strict-plugin-import`: under `DEP_VERIFY_STRICT=1`, importing a failing module rejects the import.

## How to get to it (user POV)

- `bun run verify <caller.ts>` (strict; it verifies imports too).
- `bun run verify --lenient <caller.ts>`.
- `bun run <program.ts>` / `bun test` importing the caller, with or without `DEP_VERIFY_STRICT=1`.

## Driving it with capture.sh

Preconditions:

- `$SK/doctor.sh` reports `doctor: OK` and `$RUN` exists.
- Scratch copies: `mkdir -p "$RUN/scratch/xmod" && cp examples/pass/clamp.ts examples/pass/useClamp.ts "$RUN/scratch/xmod/"`.

- **Certified caller.** Run `$SK/capture.sh "$RUN" cross-module-imports.xmod-certified -- env DEP_VERIFY_NO_CACHE=1 bun run verify examples/pass/useClamp.ts`. Exit 0, the row `examples/pass/useClamp.ts 1 0 0 0`, and `axioms used: 0`.
- **No execution.** Append `console.log("CALLEE EXECUTED");` to `$RUN/scratch/xmod/clamp.ts`. Run `$SK/capture.sh "$RUN" cross-module-imports.xmod-no-execution -- env DEP_VERIFY_NO_CACHE=1 bun run verify "$RUN/scratch/xmod/useClamp.ts"`. Exit 0 with a certified row, and `CALLEE EXECUTED` appears nowhere in the log. Remove the line again before the next step.
- **Uncertified import.** Run `$SK/capture.sh "$RUN" cross-module-imports.xmod-uncertified-import -- env DEP_VERIFY_NO_CACHE=1 bun run verify test/e2e/fixtures/callUncertified.ts || true`. Exit 1, and stderr contains `error[uncertified]: the imported declaration `badAdd` is not certified in …/uncertified.ts`. The caller's own row still reads `1 0 0 0`: the failure is the import. Repeat with `--lenient` (label `.lenient`). Exit 0.
- **Weakened callee postcondition.** In `$RUN/scratch/xmod/clamp.ts`, change `@post lo <= result && result <= hi` to `@post lo <= result`. Run `$SK/capture.sh "$RUN" cross-module-imports.xmod-spec-weakened -- env DEP_VERIFY_NO_CACHE=1 bun run verify "$RUN/scratch/xmod/useClamp.ts" || true`. Exit 1, with `useClamp.ts:7:3: error[post]: postcondition `0 <= result && result <= 100` may not hold` and the row `0 0 1 0`. Restore the line.
- **Strengthened callee precondition.** Change `@pre lo <= hi` to `@pre lo + 200 <= hi` in the scratch `clamp.ts`, and rerun the previous command (label `.xmod-pre-strengthened`). Exit 1, with `useClamp.ts:7:10: error[pre-call]: a precondition of the call may not hold: `lo + 200 <= hi`` at the `clamp(p, 0, 100)` call, and the row `0 0 1 0`.
- **Strict plugin import.** Run `$SK/capture.sh "$RUN" cross-module-imports.xmod-strict-plugin-import -- env DEP_VERIFY_NO_CACHE=1 DEP_VERIFY_STRICT=1 bun run test/e2e/fixtures/importFailing.ts || true`. Exit 1; stderr has `clampNoPre.ts` `error[post]` diagnostics; stdout lacks `the failing example was imported despite strict mode`. Without `DEP_VERIFY_STRICT` (label `.lenient`), you get exit 0 and that line, after the same diagnostics printed as warnings.

## Gotchas

- Verifying only the caller checks the callee's certification but does not print the callee's
  own diagnostics. A failing callee shows up as one `<caller>:1:1: error[uncertified]: the
  imported declaration `<name>` is not certified in <callee path>`, while the caller's row can
  still read `1 0 0 0`. Run the CLI on the callee to see why.
- Counterexamples at call sites can name solver-internal values, such as `fst ?0 = 101` for
  the callee's result. Evaluate only the named parameters.
- The cache key includes the hashes of the transitive imports. Running warm after a callee
  edit is still correct, but run cold anyway so the timing does not mislead.
- Imports resolve relative to the file. Copy the caller together with its callee (keeping the
  same relative layout), or the caller fails to resolve rather than failing verification.
- `test/e2e/fixtures/importFailing.ts` has no spec of its own, so `bun run verify` on it
  reports `no annotated function to verify`. Drive it with `bun run`, not the CLI.
