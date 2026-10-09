---
name: verify-formver
description: Drive formver-ts (the dep-verify build-time dependent-type verifier for TypeScript on Bun) through its real user surfaces, namely the `bun run verify` CLI, the preload plugin under `bun run` and `bun test`, `Bun.build` production builds, cross-module specs and the `.dep-verify` verdict cache, and capture transcripts as proof. Use it after changing anything in src/, scripts/ or examples/, when reproducing a verifier or plugin bug, or before claiming a feature works. To check whether "certified" really means the spec holds, use verify-formver-soundness.
---

# Verify formver-ts

formver-ts reads JSDoc tags on plain TypeScript functions, proves them with Z3 and a trusted
kernel, and injects runtime checks for anything it could not certify. Users touch it in four
places, and the CLI is the primary one:

| surface | entry point | what it does |
|---|---|---|
| CLI | `bun run verify [paths…] [--lenient]` | static verification, diagnostics, summary table; never runs code |
| runtime plugin | `bun run <file.ts>` / `bun test` from the repo root (bunfig preload) | verifies on import, injects same-line runtime checks |
| bundler plugin | `Bun.build({ plugins: [depVerifyPlugin] })` | same, plus `NODE_ENV=production` stripping |
| walkthrough | `bun run demo` | 7 self-checking steps over all of the above |

There is no server. Every drive is a short-lived `bun` process.

All paths below are relative to the repo root; `SK=.agents/skills/verify-formver/scripts`.

## Launch

Once per checkout:

```sh
bun install      # devDependencies only (typescript, @types/bun), needed for `bun run typecheck`
bun run setup    # idempotent; stdout is exactly `Z3 5.1.0.0` when .z3/libz3.so loads
```

Per verification run:

```sh
SK=.agents/skills/verify-formver/scripts
RUN=$($SK/new-run.sh <feature-id>)   # prints /tmp/formver-verify/<stamp>-<feature-id>-<pid>
```

Ready means `$RUN/evidence/RUN.txt` exists (it records the HEAD commit, the dirty-file count
and the Bun version). Teardown is `$SK/cleanup.sh "$RUN"`, described below.

Rules that keep a run honest:

- **Cold by default.** Prefix every verification with `env DEP_VERIFY_NO_CACHE=1`. A warm
  `.dep-verify/cache` answers in about 0.1 s and proves nothing about the current code. Only
  the verdict-cache feature runs warm, on purpose. A cold `examples/pass` takes 15–30 s,
  mostly `binarySearch`.
- **Scratch only.** Write or copy every program you drive into `$RUN/scratch/`. Never edit
  `examples/` or `test/e2e/fixtures/`: tests, the demo and other recipes depend on them. Never
  put programs in `src/`, `test/` or `scripts/`, because the plugin deliberately skips those
  directories and nothing would be verified.
- **The working directory decides whether the plugin runs.** From the repo root,
  `bunfig.toml` preloads `src/preload.ts` for both `bun run` and `bun test`. From any other
  directory (for example `--cwd "$RUN/scratch"` below) code runs raw, with no verification and
  no checks, unless you pass `bun --preload <repo>/src/preload.ts`. Use that difference to
  show what the plugin adds.
- **Modes.** The CLI is strict by default (`--lenient` relaxes it). The plugin is lenient by
  default (`DEP_VERIFY_STRICT=1` makes it strict). `NODE_ENV=production` affects only
  injection, never verdicts.

## Doctor

```sh
.agents/skills/verify-formver/scripts/doctor.sh
```

It is read-only: its smoke run uses `DEP_VERIFY_NO_CACHE=1`, so it writes nothing. It checks
the Bun version (1.4.2 expected), that Z3 loads (it prints the version and the library path,
honouring `DEP_VERIFY_LIBZ3`), the two bunfig preloads, `node_modules/typescript`, and a cold
strict verification of `examples/pass/clamp.ts` (`1 0 0 0`, `axioms used: 0`). It ends with
`doctor: OK` or `doctor: FAILED (n problem(s))`. Run it first, and again whenever output looks
wrong. Do not drive a checkout whose doctor fails; report the failing line instead.

## Drive

Wrap every command that is part of a proof in `capture.sh`:

```sh
$SK/capture.sh "$RUN" <feature>.<sub-feature> [--cwd DIR] -- <command…>
$SK/capture.sh "$RUN" cli-verify.cli-pass -- env DEP_VERIFY_NO_CACHE=1 bun run verify examples/pass
$SK/capture.sh "$RUN" runtime-checks.raw --cwd "$RUN/scratch" -- bun main.ts || true
```

It exits with the command's own code, so append `|| true` where failure is the expected outcome.

The recipes live in the feature map: [`features/README.md`](features/README.md). Pick the
feature your change touches and drive **every** entry point its file lists; one convenient
path is not a proof of the others.

Stable handles to match on (from `src/cli.ts`, `src/diagnostics.ts`, `src/inject/runtime.ts`):

- Summary table: header `file  certified  smt-only  failed  rejected`, one row per file
  (`^<path> +<c> +<s> +<f> +<r>$`, path as given on the command line), a `total` row, then
  `axioms used: 0` and `N file(s) verified, M function(s) with a verdict`. It goes to stdout.
- Diagnostics: `<path>:<line>:<col>: error[<kind>]: <message>`, optionally followed by
  `  counterexample: a = 1, b = 2`. Uncertified-but-proved obligations print
  `warning[uncertified]`. They go to stderr.
- Exit codes: `0` ok, `1` verification failure, `2` usage error. `bun run` adds its own stderr
  line, `error: script "verify" exited with code 1`.
- Runtime errors: `PreconditionError: <fn>: precondition `<spec>` failed at <file>:<line>:<col> (<args>)`,
  `PostconditionError`, and `ObligationError: <kind> check `<spec>` failed at …`.

Broad regression baselines (run them when the change is wide, and capture them too):

- `bun run demo`: 7 steps, exits non-zero if any step misbehaves. It reads the cache, so run
  it with `env DEP_VERIFY_NO_CACHE=1` for a cold run (about 30 s).
- `bun test`: about 95 s; 926 tests at the time of writing.
- `bun run typecheck`.

These complement the feature recipes; they do not replace them.

## Evidence

Everything goes to `$RUN/evidence/`, which survives cleanup:

- `NN-<label>.log` from `capture.sh`: the command, cwd, the `DEP_VERIFY_*`/`NODE_ENV`
  variables in effect, stdout, stderr, exit code and duration.
- `inputs/`: cleanup copies every scratch `.ts` here, so the proof names the exact sources.
- `build/`: bundles and `markers.tsv` from `build-check.ts`.
- `RUN.txt`: HEAD, dirty files, Bun version, start and cleanup times.

Proof standards for this repo:

- **Use the real path.** Use the CLI, `bun run` with the preload, `bun test` with the preload,
  and `Bun.build` with `depVerifyPlugin`. Do not import `verify()` or `verifyCached()` into a
  script and call that a proof.
- **Pair every claim.** Each claim needs a must-pass case and a must-fail case. A verifier that
  rejects everything also "rejects the broken example".
- **Show the action and the result:** the full transcript and exit code, not a summary line.
- **Evaluate counterexamples; never compare them.** Z3 picks the values. Copy them into a
  scratch program, run it raw, and show that the spec or obligation is actually false at
  those values.
- **Compute line numbers.** Same-line injection is a guarantee. Assert that a stack frame's
  line equals `grep -n` on the source, not a number you typed.
- **Check side effects:** the bundles on disk for build claims; `.dep-verify/cache` entries
  (a count delta plus the JSON `path`/`sourceHash`/`imports`) for cache claims; and
  `git status --porcelain` is unchanged at the end, so you never touched tracked files.
- **Production stripping is a claim about absence.** Show the marker in the development
  bundle and its absence from the production bundle; an absence alone could be a failed build.

## Cleanup

```sh
.agents/skills/verify-formver/scripts/cleanup.sh "$RUN"
```

It kills only the PIDs you appended to `$RUN/pids` (`echo $! >> "$RUN/pids"` after
backgrounding anything). It then archives the scratch sources into `evidence/inputs/`, deletes
`scratch/`, and deletes the `.dep-verify/cache` entries created during the run whose `path`
points into `$RUN`. Cache entries for repository files stay, since they are valid cache. It
refuses any directory outside `/tmp/formver-verify` (or `$FORMVER_VERIFY_ROOT`) and any
directory without `evidence/RUN.txt`. Run it after every attempt, failed ones included. The
evidence stays at `$RUN/evidence/`.

Never `pkill bun` or kill by name, because the editor and other agents run Bun too. Never wipe
`.dep-verify/` or `.z3/` wholesale.

**Isolation.** Runs are isolated by their `$RUN` directories, so two agents can drive side by
side. They share three things, none of which can be redirected:

- `.z3/`, which is read-only;
- `.dep-verify/cache/`, which is content-addressed and safe to share, but which you count by
  your own `$RUN` paths rather than by total size, because a concurrent run also adds entries;
- the working tree. Do not edit it while someone else is verifying it.

## Helpers

All of them are executable; run them from the repo root.

| helper | invocation | purpose |
|---|---|---|
| `new-run.sh` | `RUN=$($SK/new-run.sh <label>)` | create `$RUN/{scratch,evidence}`, snapshot the cache listing |
| `doctor.sh` | `$SK/doctor.sh` | read-only health check, ends in `doctor: OK` |
| `capture.sh` | `$SK/capture.sh "$RUN" <label> [--cwd DIR] -- <cmd…>` | transcript plus exit code into `evidence/NN-<label>.log` |
| `build-check.ts` | `bun $SK/build-check.ts "$RUN/evidence/build" <entry.ts…>` | `Bun.build` with the plugin in development and production, write bundles, count every injected check |
| `cleanup.sh` | `$SK/cleanup.sh "$RUN"` | kill recorded PIDs, archive inputs, remove scratch and this run's cache entries |
