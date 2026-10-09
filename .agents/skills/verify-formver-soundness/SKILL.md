---
name: verify-formver-soundness
description: Red-team formver-ts (the dep-verify dependent-type verifier for TypeScript on Bun) to check that "certified" really means the spec holds. It mutates verified examples, checks certified functions with an independent JavaScript oracle, runs syntax and semantics probes against the parser, and attacks the trusted kernel directly. Use it after any change to src/kernel, src/vc, src/extract, src/syntax, src/verify.ts or the elaborator, before trusting a new fragment feature, or when a verdict looks too good. For ordinary end-to-end behavior (CLI, plugin, builds, cache), use verify-formver.
---

# Verify formver-ts soundness

A verifier is correct when it never certifies a program that breaks its spec. It also needs
to certify enough to be useful, but that matters less. `bun test` and `bun run demo` check
behavior that someone anticipated. This skill hunts for what nobody anticipated, using
evidence that does not trust the verifier.

- **The oracle** (`fuzz-post.sh`) reads signatures and spec tags with regular expressions,
  evaluates the spec text as plain JavaScript, and calls the function Bun actually loads. It
  shares no code with the verifier's parser, extraction, elaboration or interpreter, so it
  catches bugs that those components share (`test/difftest` compares the verifier against its
  own interpreter, and cannot).
- **The verdict** comes from the real CLI, `bun src/cli.ts` (the same program as
  `bun run verify`), run cold in strict mode.
- **A soundness bug** is a `certified` verdict plus a concrete oracle violation, or a hang
  (termination is part of what certification claims). Everything else is either a correct
  rejection or a completeness gap.

This skill reuses the run lifecycle of `verify-formver`. Read its `SKILL.md` for the scratch,
cache and plugin-mode rules; they apply here unchanged.

```sh
SK=.agents/skills/verify-formver/scripts           # run lifecycle: new-run, doctor, capture, cleanup
SS=.agents/skills/verify-formver-soundness/scripts # this skill's tools
```

## Launch

There is no server. With `bun run setup` done once per checkout:

```sh
RUN=$($SK/new-run.sh soundness-<feature-id>)
```

Ready means `$RUN/evidence/RUN.txt` exists.

## Doctor

```sh
$SK/doctor.sh                                   # must end in `doctor: OK`
$SS/fuzz-post.sh examples/fail/clampNoPre.ts    # the oracle must find violations here (exit 1)
$SS/fuzz-post.sh examples/pass/clamp.ts         # and none here (exit 0)
```

All three commands are read-only. If the oracle fails to flag `clampNoPre`, or flags `clamp`,
stop: the harness is broken, and nothing it says about the verifier counts.

## Drive

The recipes are in the feature map, [`features/README.md`](features/README.md). Each tool
prints one line per item and writes a TSV under `$RUN/evidence/`:

| tool | invocation | output |
|---|---|---|
| oracle | `$SS/fuzz-post.sh [--with-plugin] <file.ts> [--fn f] [--count N] [--seed S] [--gen g.ts] [--json out.json]` | per-function findings; exit 0 clean, 1 finding, 2 untestable, 3 hang |
| mutants | `$SS/run-mutants.sh "$RUN" <file.ts> [--max N] [--count N] [--gen g.ts]` | `evidence/mutants-<name>.tsv` plus per-mutant verifier and oracle logs |
| probes | `$SS/run-probes.sh "$RUN" [probe…]` | `evidence/probes.tsv` plus per-probe logs |
| kernel | `bun $SS/kernel-attack.ts <attacks.ts>` | one line per attack; exit 1 on any accepted attack or failed control |

Wrap each invocation in `$SK/capture.sh "$RUN" <label> -- …` so the summary output and exit
code are kept too. The tools already write their detailed logs into `$RUN/evidence/`.

`run-mutants.sh` and `run-probes.sh` run the oracle twice per item, raw and under the plugin,
and print `raw=X plugin=Y`. Both runs matter. Some bugs only show with the plugin: a call
that breaks a helper's `@pre` but happens to return an acceptable value is clean raw and is
caught only by the injected precondition check (`neq-call`). Others only show when the two
disagree: a return value changed by injection (`comma-operator`).

Classes you will see, and what to do about each:

| class | meaning | action |
|---|---|---|
| `SOUNDNESS-BUG` | certified, but the oracle has a concrete violation or a hang | Stop. Minimize it (one function, smallest input), keep the evidence, and report it. Do not "fix" the probe. |
| `SMT-BUG` | Z3 proved a false obligation (`smt-only` plus a violation) | Report it; the VC generation or the SMT encoding is wrong. |
| `INJECTION-BUG` | the raw oracle run violates the spec but the plugin run is clean | Report it. The plugin only adds throws and both runs see the same inputs, so the injected code changed a return value. Bundle the file with `$SK/build-check.ts` to see the edit. |
| `CRASH` | `error[internal]`, an exit code other than 0 or 1, or a timeout | Report it with the input. |
| `CHECK-PROBE` | the oracle contradicts the probe's own claim | Fix the probe (or its generator) first. |
| `survived` | certified, and the oracle is clean | Argue in one line why the mutant is equivalent (for example, `x >= hi` returns `hi` when `x === hi` either way). |
| `killed-oracle-clean` / `incomplete` | not certified, oracle clean | A completeness gap or an equivalent mutant. Note it, and check it is a listed known limit. |
| `killed` / `ok` | the expected outcome | Nothing to do. |

## Evidence

Everything stays under `$RUN/evidence/` after cleanup:

- `mutants-<name>.tsv` and `mutants-<name>/NNN.{verify,oracle,oracle-plugin}.log`: every
  mutant's verdict and both oracle results. The mutated sources are archived to `inputs/mutants/<name>/NNN/` by
  cleanup, each with its `MUTATION.txt`.
- `probes.tsv` and `probes/<probe>.{verify,oracle,oracle-plugin}.log`.
- `NN-<label>.log` from `capture.sh` (attack runs, oracle runs, baselines).

Proof standards:

- **A bug report needs both halves:** the verifier's `certified` row (verify log) and the
  oracle's concrete input and result (oracle log). Re-run that input in a raw scratch program
  to confirm it outside the oracle.
- **"Nothing found" says how hard you looked:** the files, mutant counts and classes, probe
  count, oracle `--count` and `--seed`, and how many inputs satisfied the preconditions (an
  oracle run with `0/N` satisfying inputs checked nothing).
- **Run cold.** Every tool here already verifies with `DEP_VERIFY_NO_CACHE=1`.
- **Never weaken a probe or a spec to make a red row go away.** The row is the finding.

## Cleanup

```sh
$SK/cleanup.sh "$RUN"
```

It archives the scratch sources (mutants, copied probes, attack files) into `evidence/inputs/`,
deletes `scratch/`, removes any cache entries pointing into the run, and keeps `evidence/`. The
oracle always runs from `${TMPDIR:-/tmp}/formver-fuzz-cwd`, an empty directory left in place
on purpose (it must never contain a `bunfig.toml`). The tools kill their own children through
`timeout`; if you background a run yourself, `echo $! >> "$RUN/pids"` so cleanup can kill it.
Never `pkill bun`.

Isolation: same as `verify-formver`. Runs are separate directories; the shared cache is not
used here (every verification is cold), so concurrent soundness runs do not interfere.

## Helpers

| helper | invocation | purpose |
|---|---|---|
| `fuzz-post.sh` | `$SS/fuzz-post.sh [--with-plugin] <file.ts> [opts]` | independent oracle in raw or plugin mode, with a 60 s cap (`FUZZ_POST_TIMEOUT`) |
| `fuzz-post.ts` | invoked by `fuzz-post.sh` | the oracle itself; `--gen` takes a generator for union parameters |
| `mutate.ts` | `bun $SS/mutate.ts <file.ts> <out-dir> [--max N]` | write single-change mutants (used by `run-mutants.sh`) |
| `run-mutants.sh` | `$SS/run-mutants.sh "$RUN" <file.ts> [--max N] [--count N] [--gen g.ts]` | mutate, verify and fuzz, then classify |
| `run-probes.sh` | `$SS/run-probes.sh "$RUN" [probe…]` | the 30 shipped syntax and semantics probes in `probes/` |
| `kernel-attack.ts` | `bun $SS/kernel-attack.ts <attacks.ts>` | run attacks and controls against `src/kernel/index.ts` |
| `attacks.example.ts` | `cp $SS/attacks.example.ts "$RUN/scratch/attacks.ts"` | starter attack file: 3 controls and 5 attacks |
| `probes/union-rect.gen.ts` | `--gen .agents/skills/verify-formver-soundness/probes/union-rect.gen.ts` | oracle generator for one-parameter `Shape` functions (also `examples/pass/shape.ts`) |
