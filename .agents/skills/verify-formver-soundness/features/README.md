# formver-ts soundness map

This directory is the maintained source for checking that formver-ts never certifies a wrong
program. Read this index, then use the matching feature file as the recipe. For CLI, plugin,
build and cache behavior, see [`../../verify-formver/features/`](../../verify-formver/features/README.md).

## Baseline preconditions

- `SK=.agents/skills/verify-formver/scripts` and `SS=.agents/skills/verify-formver-soundness/scripts`, with commands run from the repo root.
- `$SK/doctor.sh` prints `doctor: OK`.
- The oracle self-check passes: `$SS/fuzz-post.sh examples/fail/clampNoPre.ts` exits 1, and `$SS/fuzz-post.sh examples/pass/clamp.ts` exits 0.
- `RUN=$($SK/new-run.sh soundness-<feature-id>)` exists.

## Driving conventions

- Verdicts come from the real CLI, cold and strict. The tools do this for you.
- Ground truth comes from the oracle, which runs the function as Bun loads it. Raw mode (the
  default) tests the program as written; `--with-plugin` also runs the injected checks.
- Every red class (`SOUNDNESS-BUG`, `SMT-BUG`, `INJECTION-BUG`, `CRASH`, `CHECK-PROBE`) is investigated before
  anything else. Keep its logs.
- Wrap each tool invocation in `$SK/capture.sh "$RUN" <feature>.<sub-feature> -- …`.

## Proof and skip reporting

- Mutation proof: the TSV, the class counts, and a one-line equivalence argument for every `survived` row.
- Oracle proof: the per-function `satisfied/generated` counts and `--seed`; `0/N` means untested.
- Probe proof: the full `probes.tsv`, plus the README known limit for each `incomplete` row.
- Kernel proof: the attack file (archived by cleanup) and the run log, with every control passing.
- Report files or functions you could not test (for example, a union parameter without a generator) as skipped, with the reason.

## Feature entry contract

Each feature file starts with an H1 title and one paragraph describing what is being protected.
It then uses exactly four H2 sections in this order: `Sub-features`,
`How to get to it (user POV)`, `Driving it with the soundness tools`, and `Gotchas`.

## Features

- [Mutation rejection](./mutation-rejection.md): single-change mutants of certified files must not be certified unless they are equivalent.
- [Independent oracle](./independent-oracle.md): every certified function meets its postconditions and the safe-integer model on concrete inputs, raw and under the plugin.
- [Parser and semantics probes](./parser-probes.md): programs whose meaning hinges on JavaScript syntax corners (ASI, associativity, literals, shadowing, fall-through).
- [Kernel attacks](./kernel-attacks.md): direct attempts to make the trusted kernel accept a proof of false or a bogus conversion.
