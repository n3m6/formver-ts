# Runtime checks

Under `bun run` and `bun test`, the preload plugin verifies every imported `.ts`/`.mts` file
that carries a spec tag. It then injects runtime checks on the same source lines (exported
preconditions, boundary guards, and every obligation that was not certified), so a violated
precondition throws a named error that points at the function's own line. The plugin is
lenient by default (it warns and checks); with `DEP_VERIFY_STRICT=1` it refuses to load a file
that does not verify.

## Sub-features

- `rt-precondition`: `examples/runtime/main.ts` prints `20`, then throws `PreconditionError` for `safeGet([10, 20, 30], 5)`.
- `rt-line-accuracy`: the top stack frame is `safeGet.ts:<line of "export function safeGet">`, because injection adds no lines.
- `rt-raw-contrast`: the same program without the plugin prints `20` and `undefined`, with no error.
- `rt-lenient-uncertified`: importing a failing file warns with its diagnostics, runs, and throws `ObligationError` only on a bad input.
- `rt-strict-refusal`: with `DEP_VERIFY_STRICT=1` the failing import throws at load time, so the program body never runs.
- `rt-bun-test`: the plugin is preloaded for `bun test`; an out-of-bounds call throws inside a test.
- `rt-lenient-unextracted`: an exported function the extractor cannot build (missing return type, `boolean` return, an index inside a spec) still keeps its `@pre` check in lenient mode, as the README's injection table promises. **Fails at `8135f5b`**: nothing is injected.

## How to get to it (user POV)

- `bun run <file.ts>` from the repo root (bunfig preload).
- `bun test <file>` from the repo root (the `[test]` preload).
- `bun --preload <repo>/src/preload.ts <file.ts>` from any directory.
- `DEP_VERIFY_STRICT=1` with any of the above.

## Driving it with capture.sh

Preconditions:

- `$SK/doctor.sh` reports `doctor: OK` and `$RUN` exists.
- The scratch copies exist: `mkdir -p "$RUN/scratch/runtime" "$RUN/scratch/pass" "$RUN/scratch/fail" && cp examples/runtime/main.ts "$RUN/scratch/runtime/" && cp examples/pass/safeGet.ts "$RUN/scratch/pass/" && cp examples/fail/offByOne.ts "$RUN/scratch/fail/"`.

- **Precondition fires.** Run the shipped example under the plugin. Run `$SK/capture.sh "$RUN" runtime-checks.rt-precondition -- env DEP_VERIFY_NO_CACHE=1 bun run examples/runtime/main.ts || true`. Exit 1; stdout is `20`; stderr has `PreconditionError: safeGet: precondition `0 <= i && i < a.length` failed at examples/pass/safeGet.ts:2:4 (a = [3 elements], i = 5)`. The location may be absolute; `2:4` is where the `@pre` text sits.
- **Line accuracy.** Compare the stack frame with the source. Run `grep -n "export function safeGet" examples/pass/safeGet.ts`, which prints line `4`. The first `at … safeGet.ts:<n>:<col>` frame in the previous log has `<n>` equal to that line.
- **Raw contrast.** Run the copied program without the plugin. Run `$SK/capture.sh "$RUN" runtime-checks.rt-raw-contrast --cwd "$RUN/scratch/runtime" -- bun main.ts`. Exit 0; stdout is `20` then `undefined`. Then run the copy with the plugin: `$SK/capture.sh "$RUN" runtime-checks.rt-precondition.scratch --cwd "$RUN/scratch/runtime" -- env DEP_VERIFY_NO_CACHE=1 bun --preload "$PWD/src/preload.ts" main.ts || true`. You get the same `PreconditionError` as the shipped run, located in the scratch `safeGet.ts`.
- **Lenient, uncertified.** Write `$RUN/scratch/fail/main.ts`: `import { offByOne } from "./offByOne"; console.log(offByOne([1, 2, 3], 2)); console.log(offByOne([1, 2, 3], 3));`. Run `$SK/capture.sh "$RUN" runtime-checks.rt-lenient-uncertified --cwd "$RUN/scratch/fail" -- env DEP_VERIFY_NO_CACHE=1 bun --preload "$PWD/src/preload.ts" main.ts || true`.
  - Stderr first shows `offByOne.ts:5:10: error[index]` with a counterexample.
  - Stdout is `3`, from the valid call.
  - The out-of-bounds call then throws `ObligationError: index check `0 <= i && i < a.length` failed at …offByOne.ts:5:10 (i = 3, a.length = 3)`. Exit 1.

  Run raw for contrast: `--cwd "$RUN/scratch/fail" -- bun main.ts` prints `3` and `undefined`.
- **Strict refusal.** Repeat the lenient run with `DEP_VERIFY_STRICT=1` added to the `env` list (label `.strict`). Exit 1; stderr is the `error[index]` diagnostic thrown from `src/plugin.ts`; stdout is empty because `main.ts` never ran. The shipped equivalent is `env DEP_VERIFY_NO_CACHE=1 DEP_VERIFY_STRICT=1 bun run test/e2e/fixtures/importFailing.ts`. It exits 1, and its stdout lacks `the failing example was imported despite strict mode`. Without `DEP_VERIFY_STRICT` it exits 0 and prints that line after the warnings.
- **Under bun test.** Write `$RUN/scratch/safeGet.test.ts` importing `safeGet` from `<repo>/examples/pass/safeGet` with two tests: `expect(safeGet([10, 20, 30], 1)).toBe(20)` and `expect(() => safeGet([10, 20, 30], 5)).toThrow(/precondition/)`. Run `$SK/capture.sh "$RUN" runtime-checks.rt-bun-test -- env DEP_VERIFY_NO_CACHE=1 bun test "$RUN/scratch/safeGet.test.ts"`, which reports `2 pass`, `0 fail`. Then run the same file from scratch (no preload): `--cwd "$RUN/scratch" -- bun test ./safeGet.test.ts || true`, which reports `1 pass`, `1 fail`, proving the check came from the plugin.
- **Lenient, unextracted.** Write `$RUN/scratch/noret.ts`, an exported function with `@pre 0 <= n` and `@post 0 <= result` but **no return type**: `export function noRet(n: number) { return n; }`. Run `$SK/capture.sh "$RUN" runtime-checks.rt-lenient-unextracted -- env DEP_VERIFY_NO_CACHE=1 bun -e "import { noRet } from '$RUN/scratch/noret.ts'; console.log(noRet(-3));" || true` from the repo root.
  - Expected (README injection table: "`@pre` of an exported function: keep"): `PreconditionError`, exit 1.
  - Observed at `8135f5b`: stdout `-3`, exit 0, and no check at all. The CLI on the same file exits 1, and the strict plugin refuses the import, so only lenient mode fails open.
  - The same happens for a `boolean` return type and for `@post result === a[1]` (an index in a spec; see the `spec-index` probe in the soundness skill). Confirm with `bun $SK/build-check.ts "$RUN/evidence/build/noret" "$RUN/scratch/noret.ts"`, which counts 0 for every marker.

## Gotchas

- The plugin skips `src/`, `test/` and `scripts/` of this repo by path, and any file without a
  spec tag. A scratch program that imports nothing annotated shows nothing.
- An `ObligationError` for an internal check (index, range, slice) reports `fn: ""`. Identify
  the function by its location, not its name.
- `NODE_ENV=production` changes what is injected. Keep it unset (or `development`) here; the
  production rules are in [production builds](./production-build.md).
- The precondition message's location is the spec text (`safeGet.ts:2:4`), while the stack
  frame points at the function line (`safeGet.ts:4`). Assert each against its own source line.
- `bun run` without `DEP_VERIFY_NO_CACHE=1` reuses cached verdicts and injection plans, so the
  diagnostics still print but come from the cache.
