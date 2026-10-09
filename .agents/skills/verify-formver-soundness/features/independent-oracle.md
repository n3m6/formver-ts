# Independent oracle

Every certified function must meet its postconditions on every input that satisfies its
preconditions. A declared `number` result must also be a safe integer, because that is the
verifier's model. The oracle checks this on concrete inputs without using any verifier code.
In plugin mode, it also checks that no injected runtime check fires on a valid input.

## Sub-features

- `oracle-raw`: certified functions in `examples/pass` show no finding when run as written.
- `oracle-plugin`: the same functions under the preload plugin throw no `PreconditionError`, `PostconditionError` or `ObligationError` on valid inputs.
- `oracle-negative`: `examples/fail` files with a postcondition or range defect show findings, which proves the oracle can see them.
- `oracle-union`: `shape.ts` is checked through the `Shape` generator.
- `oracle-new-code`: any newly certified file (yours, or one added to `examples/pass`) gets the same treatment.

## How to get to it (user POV)

- A user trusts `certified` and ships the function, possibly with production stripping its
  checks. The oracle asks whether that trust holds at runtime.

## Driving it with the soundness tools

Preconditions:

- The baseline preconditions in `README.md` hold, and `$RUN` exists.
- `bun run verify examples/pass` is all `1 0 0 0` (only certified functions are interesting here).

- **Raw, every pass file.** Run `for f in examples/pass/*.ts; do $SK/capture.sh "$RUN" independent-oracle.oracle-raw.$(basename "$f" .ts) -- $SS/fuzz-post.sh "$f" --count 1000 --json "$RUN/evidence/oracle-$(basename "$f" .ts).json"; done`. Every file reports `result: OK` (exit 0) except `shape.ts`, which reports `NOTHING TESTED` (exit 2, needs `--gen`). `sumTo` shows stack-overflow throws for large `n`, which are not findings. `safeGet` has no postcondition, so only its result type and throws are checked.
- **Union.** Run `$SK/capture.sh "$RUN" independent-oracle.oracle-union -- $SS/fuzz-post.sh examples/pass/shape.ts --count 1000 --gen .agents/skills/verify-formver-soundness/probes/union-rect.gen.ts`. You get `result: OK`.
- **Under the plugin.** Repeat the raw loop with `env DEP_VERIFY_NO_CACHE=1 $SS/fuzz-post.sh --with-plugin …` (label `.oracle-plugin.<name>`). The mode line reads `mode plugin`, and every file is `OK`. An `UNEXPECTED-THROW` naming a dep-verify error class on a certified function is a soundness bug: an obligation the verifier claimed was proved fails at runtime.
- **Negative control.** Run `$SK/capture.sh "$RUN" independent-oracle.oracle-negative.post -- $SS/fuzz-post.sh examples/fail/clampNoPre.ts || true`, which finds `POST` violations (exit 1). The same with `examples/fail/overflow.ts` finds `RANGE` findings. With `--with-plugin` on `examples/fail/offByOne.ts`, you get `UNEXPECTED-THROW … ObligationError: index check`, while raw it is `OK`, because there is no postcondition and an out-of-bounds read returns `undefined`.
- **Vary the seed** before you claim nothing was found: rerun the raw loop with `--seed 2` and `--seed 3`.

## Gotchas

- Read the `satisfied/generated` counts. A restrictive precondition can leave very few valid
  inputs, and `0/N` prints a `WARNING`: nothing was checked.
- The built-in generator handles `number`, `boolean`, `number[]` and generic `T[]` (filled
  with integers). Anything else needs `--gen`, a module whose default export is
  `(fn, rng) => args[] | undefined`. See `probes/union-rect.gen.ts`.
- Specs are evaluated with the module's exports in scope, so a spec can call another
  exported function. A spec that does not parse as JavaScript is reported as skipped.
- Bun's engine has proper tail calls: endless tail recursion loops forever instead of
  overflowing the stack. The wrapper's 60 s cap (`FUZZ_POST_TIMEOUT`) turns that into exit 3,
  `TIMEOUT`.
- Raw mode depends on the working directory, so always go through `fuzz-post.sh`. Running
  `bun fuzz-post.ts` from the repo root silently loads the plugin.
- Plugin mode verifies the target with the shared cache unless `DEP_VERIFY_NO_CACHE=1` is set.
- `run-mutants.sh` and `run-probes.sh` always run both modes with the same seed, so they see
  the same inputs. Plugin mode can only add throws. If raw finds a violation and plugin mode
  is clean, the injected code changed a value, and the runners classify that as
  `INJECTION-BUG`. When you run the oracle by hand, compare both modes the same way.
