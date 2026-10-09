# Mutation rejection

A certified function changed in one place (a comparison flipped, a literal moved by one, a
precondition or invariant conjunct dropped) usually no longer meets its spec. The verifier must
then stop certifying it. When a mutant is still certified, it must be equivalent, and the
independent oracle must find nothing.

## Sub-features

- `mut-code`: comparison, equality, arithmetic, `&&`/`||`, `Math.floor`/`Math.trunc`, `Math.max`/`Math.min` and literal ±1 swaps in function bodies.
- `mut-spec-strengthen`: tightening a postcondition (`<=` to `<`, and similar) must be rejected unless it still holds.
- `mut-assumption-drop`: removing a precondition, an invariant, a termination measure, or one conjunct of them.
- `mut-loop`: mutants inside loops (`binarySearch`): bounds, update steps and the invariant.
- `mut-recursion`: mutants in recursive functions (`sumTo`): base case, recursive argument and the measure.
- `mut-union`: mutants of a tagged-union function (`shape.ts`), which needs the `Shape` generator.

## How to get to it (user POV)

- A user edits a verified function and runs `bun run verify` (or loads it through the plugin).
  These mutants are those edits, and `run-mutants.sh` drives exactly that CLI.

## Driving it with the soundness tools

Preconditions:

- The baseline preconditions in `README.md` hold, and `$RUN` exists.

- **Straight-line code.** Run `$SK/capture.sh "$RUN" mutation-rejection.mut-code -- $SS/run-mutants.sh "$RUN" examples/pass/clamp.ts`. Exit 0 with 7 mutants: the precondition strengthened (`lo < hi`) and the postcondition weakened (`||`) survive, since both are equivalent or weaker claims; `x <= lo` and `x >= hi` survive as equivalent; dropping the precondition and tightening either postcondition bound are `killed`. There are no red classes. Repeat for `abs.ts`, `take.ts` and `concat.ts` (labels `.abs` and so on).
- **Loops.** Run `$SK/capture.sh "$RUN" mutation-rejection.mut-loop -- $SS/run-mutants.sh "$RUN" examples/pass/binarySearch.ts`. There are 30 mutants, and every one is verified cold and fuzzed twice; it takes about 10 minutes (603 s measured). Background it with `echo $! >> "$RUN/pids"` if you need the shell, and never start a second run on the same file in the same `$RUN` (the runner refuses with exit 2). Mutants such as `lo = mid - 1` hang the oracle: that is `killed` when the verifier rejected it, and `SOUNDNESS-BUG` if it was certified. Observed at `8135f5b`: `killed=16 killed-oracle-clean=8 survived=6`, exit 0.
- **Recursion.** Run `$SK/capture.sh "$RUN" mutation-rejection.mut-recursion -- $SS/run-mutants.sh "$RUN" examples/pass/sumTo.ts`. Dropping the measure or changing `n - 1` to `n + 1` must be `killed`. The oracle logs stack-overflow throws for large `n`; those are not findings. Observed at `8135f5b`: `killed=10 killed-oracle-clean=6 survived=3 CRASH=3 SOUNDNESS-BUG=1`, exit 1.
  - The `SOUNDNESS-BUG` is mutant `017`, `if (n === 0) return 0;` changed to `if (n !== 0) return 0;`, which is the open `!==` bug (see the `parser-probes.md` Gotchas). It is certified, yet under the plugin `sumTo(0)` recurses into `sumTo(-1)` and trips the injected precondition (`raw=clean plugin=VIOLATION`).
  - The three `CRASH` rows (`003`, `007`, `008`: the `0 <= n` precondition weakened or dropped) are rejected correctly, but they also print `error[internal]: could not elaborate sumTo: cannot prove that this call argument is in range`. That is an elaborator robustness bug, not unsoundness.
- **Unions.** Run `$SK/capture.sh "$RUN" mutation-rejection.mut-union -- $SS/run-mutants.sh "$RUN" examples/pass/shape.ts --gen .agents/skills/verify-formver-soundness/probes/union-rect.gen.ts`. Without `--gen`, every oracle result is `untestable`. Observed at `8135f5b`: `killed=8 killed-oracle-clean=6 survived=19`, exit 0. Three precondition mutants are `raw=untestable` (`NOTHING TESTED`, 0 of 30000 inputs). In `007` the flipped `!==` asks squares for `w`/`h` fields the generator never gives them. In `022` and `023` a conjunct was dropped inside a `?:`, leaving text that is not valid JavaScript.
- **Other straight-line files at `8135f5b`:** `abs` `killed=4 survived=2`; `take` `killed=6 survived=3`; `concat` `killed=2 killed-oracle-clean=3 survived=2`. All exit 0.
- **Read the table.** Run `column -t -s $'\t' "$RUN"/evidence/mutants-*.tsv`. Every `survived` row gets a one-line equivalence argument in your report. Every red row gets its verify and oracle logs quoted.

## Gotchas

- Mutants are copied next to all of their source directory's `.ts` siblings so imports resolve.
  Only the mutated file is verified.
- The operators only match spaced binary operators (` < `, ` + `), so generics (`<T>`) and unary
  minus are never touched. `return -1` gets literal mutants only.
- A literal mutant `-1` to `-0` is equivalent under the spec (`-0 === 0`).
- `--max` (default 60) keeps an even spread when there are more mutants than that. Raise it
  for an exhaustive run.
- `killed-oracle-clean` often means the oracle's inputs missed the breaking case (for example,
  a mutant that only differs at `x === MAX`). Re-run the oracle on that mutant with
  `--count 5000` before calling it equivalent.
- The oracle column reads `raw=X plugin=Y`. A mutant is "wrong" if either run shows a
  `VIOLATION` or a `HANG`. `raw=clean plugin=VIOLATION` usually means an injected
  precondition check caught a bad internal call that happened to return a fine value.
- A diagnostic that quotes `the kernel rejected the proof of <fn>#N: error[type-mismatch]: …
  but got Unit()` inside an obligation that already failed is expected. The elaborator hands the
  kernel a placeholder for a proof Z3 refuted, and the kernel rejects it. It only matters if it
  appears in a function that would otherwise be certified.
- `binarySearch` survivor `024` (`a[mid] === target` changed to `!==`) is equivalent: any
  returned `mid` satisfies the postcondition `-1 <= result && result < a.length`. Its `else` path
  is the buggy `!==` case, but the weak postcondition holds either way, so it shows nothing.
  Survivor `015` (dropping the invariant conjunct `lo <= hi`) is also equivalent: the loop guard
  `lo < hi` supplies it inside the body, and `0 <= lo && hi <= a.length` still bounds `a[mid]`.
- The conjunct-drop operator splits on `&&` textually. Inside a `?:` precondition it can cut
  across the `?`/`:` and produce text that is not valid JavaScript; the verifier rejects it as
  a parse error and the oracle reports `untestable`. Those rows say nothing either way.
