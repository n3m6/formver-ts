# formver-ts verification map

This directory is the maintained source for verifying the user-facing behavior of formver-ts.
Read this index before driving anything, then use the matching feature file as the recipe.
Soundness red-teaming (mutants, an independent oracle, parser probes, kernel attacks) lives in
[`../../verify-formver-soundness/`](../../verify-formver-soundness/SKILL.md).

## Baseline preconditions

- `SK=.agents/skills/verify-formver/scripts`, with commands run from the repo root.
- `$SK/doctor.sh` prints `doctor: OK`.
- `RUN=$($SK/new-run.sh <feature-id>)` has created this run's `scratch/` and `evidence/`.
- `git status --porcelain` is recorded before you start, so you can show it unchanged at the end.
- `examples/` and `test/e2e/fixtures/` are read-only inputs. To modify one, copy it (with any
  sibling it imports) into `$RUN/scratch/`.

## Driving conventions

- Wrap every proof command: `$SK/capture.sh "$RUN" <feature>.<sub-feature> [--cwd DIR] -- <cmd…>`.
- Verify cold (`env DEP_VERIFY_NO_CACHE=1 …`) in every recipe except `verdict-cache`.
- A recipe that needs raw, uninstrumented behavior runs with `--cwd "$RUN/scratch"`, where no
  `bunfig.toml` preloads the plugin. One that needs the plugin either runs from the repo root
  or passes `bun --preload "$PWD/src/preload.ts"`.
- Match on the stable handles listed in `SKILL.md`, not on whole-output snapshots.
- Never compare Z3 counterexample values literally. Evaluate them in a raw scratch program.
- Compute expected line numbers with `grep -n` on the source.

## Proof and skip reporting

- CLI proof: command, stdout, stderr and exit code (one `capture.sh` log per command).
- Plugin proof: the plugin run, plus the same program run raw, which shows what the plugin added.
- Build proof: the development and production bundles plus `markers.tsv` under `evidence/build/`.
- Cache proof: this run's new cache entries (`comm -13 "$RUN/cache-before.txt" <(ls .dep-verify/cache | sort)`),
  the entry's `path`/`sourceHash`/`imports`, and the timings from the capture logs.
- Every claim pairs a must-pass case with a must-fail case.
- Report an entry point you could not drive, with the command you tried and the unmet
  precondition. Do not report it as verified through a different entry point.

## Feature entry contract

Each feature file starts with an H1 title and one paragraph describing the user-visible
behavior, followed by exactly four H2 sections in this order:

1. `Sub-features`: short IDs, one line per behavior.
2. `How to get to it (user POV)`: every user entry point.
3. `Driving it with capture.sh`: starts with `Preconditions:`, then labeled bullets that pair
   each user action with an exact command and its observable result.
4. `Gotchas`: traps that can waste or invalidate a run.

## Features

- [CLI verification](./cli-verify.md): `bun run verify` on passing, failing, smt-only,
  solver-less and unannotated inputs; diagnostics, counterexamples and exit codes.
- [Runtime checks](./runtime-checks.md): the preload plugin under `bun run` and `bun test`;
  same-line `PreconditionError`, lenient injection for uncertified code (including functions
  the extractor cannot build), and strict refusal.
- [Production builds](./production-build.md): `Bun.build` with `depVerifyPlugin`; which checks
  `NODE_ENV=production` keeps and which it strips; strict build failure.
- [Cross-module specs](./cross-module-imports.md): calling a verified function from another
  file; the spec is read by parsing, uncertified imports fail strict mode, and spec edits
  propagate to callers.
- [Verdict cache](./verdict-cache.md): `.dep-verify/cache` hits, invalidation on source and
  import edits, and `DEP_VERIFY_NO_CACHE`.
