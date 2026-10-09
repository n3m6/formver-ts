# CLI verification

`bun run verify [paths…] [--lenient]` statically verifies `.ts`/`.mts` files or directories
against their JSDoc tags. It prints located diagnostics (stderr) and a per-file summary table
(stdout), and exits 0 when every function is certified. It never executes the code.

## Sub-features

- `cli-pass`: strict verification of `examples/pass` certifies 9 of 9 functions with 0 axioms; exit 0.
- `cli-default-path`: with no path argument it verifies `examples/pass`.
- `cli-fail-diagnostics`: `examples/fail` gets one located `error[<kind>]` per broken construct; exit 1.
- `cli-counterexample-real`: every counterexample actually breaks the program when run.
- `cli-smt-only`: an obligation Z3 proves but the kernel cannot certify is `smt-only`. Strict exits 1; `--lenient` exits 0.
- `cli-lenient-invalid`: `--lenient` still exits 1 on obligations that have a counterexample.
- `cli-no-solver`: without Z3, strict refuses (exit 1) and lenient reports every obligation `smt-only` (exit 0).
- `cli-no-annotation`: a file with no spec tag is an error, not a silent pass; exit 1.
- `cli-usage`: an unknown option prints usage and exits 2; `--help` prints usage and exits 0.

## How to get to it (user POV)

- `bun run verify` (defaults to `examples/pass`).
- `bun run verify <file-or-dir>… [--lenient]`.
- `bun src/cli.ts …` is the same program the script runs.

## Driving it with capture.sh

Preconditions:

- `$SK/doctor.sh` reports `doctor: OK` and `$RUN` exists.

- **Pass set.** Verify the passing examples cold. Run `$SK/capture.sh "$RUN" cli-verify.cli-pass -- env DEP_VERIFY_NO_CACHE=1 bun run verify examples/pass`. Exit 0; nine rows each `1 0 0 0` (`abs`, `binarySearch`, `clamp`, `concat`, `safeGet`, `shape`, `sumTo`, `take`, `useClamp`); `total 9 0 0 0`; `axioms used: 0`; `9 file(s) verified, 9 function(s) with a verdict`. Expect 15–30 s.
- **Default path.** Run it without arguments. Run `$SK/capture.sh "$RUN" cli-verify.cli-default-path -- env DEP_VERIFY_NO_CACHE=1 bun run verify`. You get the same nine rows and totals as the pass set.
- **Fail set.** Verify the broken examples. Run `$SK/capture.sh "$RUN" cli-verify.cli-fail-diagnostics -- env DEP_VERIFY_NO_CACHE=1 bun run verify examples/fail || true`. Exit 1. Stderr has:
  - `error[post]` in `clampNoPre.ts` (twice) and in `overflow.ts`;
  - `error[index]` in `offByOne.ts`;
  - `error[range]` in `overflow.ts`;
  - `error[measure-decrease]` in `noDecrease.ts`;
  - eight `error[fragment]` in `rejected.ts`: `any`, `as`, parameter mutation, bare `/`, `throw`, a float literal, `this` and `%`.

  The table ends `total 0 0 4 8`.
- **Counterexamples are real.** For each `counterexample:` line, write a raw program in `$RUN/scratch/` that imports the function by absolute path, calls it with exactly those values, and prints the spec's truth value. For example, for `clampNoPre.ts`'s `x = 1, lo = 1, hi = 0`, write `cex.ts`: `import { clamp } from "<repo>/examples/fail/clampNoPre"; const [x, lo, hi] = [1, 1, 0]; const result = clamp(x, lo, hi); console.log({ result, post: lo <= result && result <= hi });`. Then run `$SK/capture.sh "$RUN" cli-verify.cli-counterexample-real --cwd "$RUN/scratch" -- bun cex.ts`. It prints `post: false`. For `index`, `n_a` is `a.length` (call `offByOne([], 0)`, which returns `undefined`). For `range`, print `Number.isSafeInteger(result)`, which is `false`.
- **smt-only.** Write `$RUN/scratch/smtOnly.ts` with a precondition that has a rational solution but no integer one:
  `/** @pre -1000 <= x && x <= 1000 && x + y === 1 && x <= y && y <= x` / `@post result === 0 */ export function noIntegerInput(x: number, y: number): number { return 1; }`.
  First run `$SK/capture.sh "$RUN" cli-verify.cli-smt-only.strict -- env DEP_VERIFY_NO_CACHE=1 bun run verify "$RUN/scratch/smtOnly.ts" || true`, then the same command with `--lenient` and the label `.lenient`. Both print `warning[uncertified]: Z3 proved the post obligation … but no kernel certificate was found` and the row `0 1 0 0`. Strict exits 1; lenient exits 0.
- **Lenient does not excuse counterexamples.** Run `$SK/capture.sh "$RUN" cli-verify.cli-lenient-invalid -- env DEP_VERIFY_NO_CACHE=1 bun run verify --lenient examples/fail || true`. Exit 1, with the same `error[...]` lines as the fail set.
- **No solver.** Point at a missing library. Run `$SK/capture.sh "$RUN" cli-verify.cli-no-solver.strict -- env DEP_VERIFY_NO_CACHE=1 DEP_VERIFY_LIBZ3=/nonexistent/libz3.so bun run verify examples/pass/clamp.ts || true`. Exit 1; stderr names `/nonexistent/libz3.so`, `bun run setup` and `strict mode needs Z3`. Repeat with `--lenient` (label `.lenient`). Exit 0; row `examples/pass/clamp.ts 0 1 0 0`; the note `no SMT solver available; every obligation needs a runtime check`.
- **No annotation.** Write `$RUN/scratch/plain.ts` containing `export const x = 1;`. Run `$SK/capture.sh "$RUN" cli-verify.cli-no-annotation -- env DEP_VERIFY_NO_CACHE=1 bun run verify "$RUN/scratch/plain.ts" || true`. Exit 1; stderr contains `no annotated function to verify`.
- **Usage.** Run `$SK/capture.sh "$RUN" cli-verify.cli-usage.bad -- bun run verify --bogus || true`. Exit 2; stderr is ``unknown option `--bogus` `` and `usage: bun run verify [paths…] [--lenient]`. Then run `$SK/capture.sh "$RUN" cli-verify.cli-usage.help -- bun run verify --help`. Exit 0, with usage on stdout.

## Gotchas

- Without `DEP_VERIFY_NO_CACHE=1` the CLI answers from `.dep-verify/cache` in about 0.1 s. You
  would be proving the cache, not the verifier.
- Diagnostics are on stderr and the table on stdout. `capture.sh` keeps them apart; quote both.
- `bun run verify` adds the stderr line `error: script "verify" exited with code 1`. That is
  Bun's script runner, not a diagnostic.
- Counterexample values depend on Z3's search and can change between versions and query order.
- Directory scans skip `node_modules` and every dot-directory, so `.agents/...` files are
  ignored when you pass a parent directory. Pass files explicitly, or copy them to scratch.
- A row of `0 0 0 0` means no function received a verdict. The reason is on stderr (no
  annotation, a parse error, or a missing file).
- Strict mode also fails when an imported declaration is not certified in its own file; see
  [cross-module specs](./cross-module-imports.md).
