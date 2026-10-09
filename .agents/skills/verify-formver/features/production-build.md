# Production builds

`Bun.build` with `depVerifyPlugin` verifies and instruments every bundled file, like the
runtime plugin does. With `NODE_ENV=production` it strips the checks the kernel certified
(postconditions and internal obligations) but always keeps exported preconditions and boundary
guards, because callers are unknown and types are erased. It also keeps every check for
anything uncertified. With `DEP_VERIFY_STRICT=1`, a file that does not verify fails the build.

## Sub-features

- `build-keep`: boundary guards (`guardInt(`, `guardIntArray(`, `guardArray(`, `guardUnion(`) and exported `new PreconditionError("` survive production, with the same count as in development.
- `build-strip`: certified `new PostconditionError("`, `checkIndex(`, `checkSlice(`, `checkLength(`, `checkRange(`, `checkPre(`, `checkInvariant(`, `checkMeasure(` and `checkMeasureDecrease(` are absent from production but present in development.
- `build-keep-uncertified`: an `smt-only` postcondition keeps its `new PostconditionError("<fn>"` in production.
- `build-runs`: a production bundle of `examples/runtime/main.ts` still throws `PreconditionError` for the out-of-bounds call.
- `build-strict-fail`: with `DEP_VERIFY_STRICT=1`, bundling a failing file fails the build with its diagnostic.

## How to get to it (user POV)

- `await Bun.build({ entrypoints, plugins: [depVerifyPlugin], target: "bun" })`, with
  `depVerifyPlugin` exported by `src/plugin.ts`, and `NODE_ENV` set while the build runs.
- `bun run demo` step 6 runs the same comparison over `examples/pass`.
- `build-check.ts` is a thin wrapper over exactly that call. It runs both modes, writes the
  bundles and counts the markers.

## Driving it with capture.sh

Preconditions:

- `$SK/doctor.sh` reports `doctor: OK` and `$RUN` exists.
- `NODE_ENV` is unset in your shell (`build-check.ts` sets it per build).

- **Both modes over the pass set.** Run `$SK/capture.sh "$RUN" production-build.pass -- env DEP_VERIFY_NO_CACHE=1 bun $SK/build-check.ts "$RUN/evidence/build/pass" examples/pass/*.ts`.
  - Exit 0, and `development: ok, 9 file(s); production: ok, 9 file(s)`, after about 25 s cold.
  - In the marker table, every `build-keep` marker has `production == development > 0`.
  - Every `build-strip` marker has `development > 0` (or is absent from both, when no example produces it) and `production == 0`.
  - `markers.tsv` and the bundles `development/<name>.js` and `production/<name>.js` exist under `evidence/build/pass/`.
  - A known-good run at commit `8135f5b`, as (development, production): `guardInt(` 21/21, `guardIntArray(` 10/10, `guardArray(` 13/13, `guardUnion(` 10/10, `new PreconditionError("` 7/7; `new PostconditionError("` 17/0, `checkRange(` 18/0, `checkIndex(` 12/0, and every other strip marker 10 or 11 in development and 0 in production.
- **Read the surviving lines.** Show what production kept for `clamp`. Run `grep -h 'guardInt("clamp"\|new PreconditionError("clamp"\|new PostconditionError("clamp"' "$RUN"/evidence/build/pass/*/clamp.js`. The development bundle has all three kinds; the production bundle has the guard and the precondition but no `PostconditionError`.
- **Uncertified stays.** Write the `smt-only` file from [CLI verification](./cli-verify.md) to `$RUN/scratch/smtOnly.ts`. Run `$SK/capture.sh "$RUN" production-build.build-keep-uncertified -- env DEP_VERIFY_NO_CACHE=1 bun $SK/build-check.ts "$RUN/evidence/build/smt-only" "$RUN/scratch/smtOnly.ts"`. The build succeeds, because the plugin is lenient, and `new PostconditionError("` has `production == development > 0`.
- **The production bundle still guards.** Copy `examples/runtime/main.ts` and `examples/pass/safeGet.ts` to `$RUN/scratch/runtime/` and `$RUN/scratch/pass/`. Build it with `$SK/capture.sh "$RUN" production-build.build-runs.bundle -- env DEP_VERIFY_NO_CACHE=1 bun $SK/build-check.ts "$RUN/evidence/build/runtime" "$RUN/scratch/runtime/main.ts"`. Then run the bundle raw: `$SK/capture.sh "$RUN" production-build.build-runs --cwd "$RUN/scratch" -- bun "$RUN/evidence/build/runtime/production/main.js" || true`. Stdout is `20`; stderr has `PreconditionError: safeGet: precondition`; exit 1.
- **Strict build fails.** Copy `examples/fail/offByOne.ts` to `$RUN/scratch/offByOne.ts`. Run `$SK/capture.sh "$RUN" production-build.build-strict-fail -- env DEP_VERIFY_NO_CACHE=1 DEP_VERIFY_STRICT=1 bun $SK/build-check.ts "$RUN/evidence/build/strict" "$RUN/scratch/offByOne.ts" || true`. Exit 1. Each mode prints `build threw: Bundle failed`, followed by the plugin's `…/offByOne.ts:5:10: error[index]: the index may be out of bounds` diagnostic. The summary reads `development: FAILED, 0 file(s); production: FAILED, 0 file(s)`.

## Gotchas

- Marker counts include the runtime helper definitions that the bundler pulls in from
  `src/inject/runtime.ts`. In development a helper's definition and its calls are both
  counted, and in production an unused helper is tree-shaken away. Compare development with
  production; do not try to match an absolute count against the number of call sites.
- `NODE_ENV` is read while the plugin's `onLoad` runs. Setting it after a build started, or
  exporting it in your shell, mixes the two modes. Leave it to `build-check.ts`.
- The plugin is lenient inside `Bun.build` too. A failing file still bundles (with checks)
  unless `DEP_VERIFY_STRICT=1` is set.
- Production never strips exported preconditions. A missing `new PreconditionError("…"` in
  production is a bug, not an optimization.
- The bundles are evidence. They live under `$RUN/evidence/build/`, so cleanup keeps them.
