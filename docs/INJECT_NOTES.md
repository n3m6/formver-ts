# Injection, plugin, cache and CLI notes (milestone 8)

Files: `src/inject/runtime.ts` (no dependencies), `src/inject/inject.ts`, `src/cache.ts`,
`src/plugin.ts`, `src/preload.ts`, `src/cli.ts`.  Specification sections 4.4, 6.5, 6.6, 6.7.

## Injection rules (`inject(source, plan, options)`)

Every edit is an **insertion inside an existing line**: no `\n` is ever inserted, nothing is
deleted, and stack-trace line numbers therefore stay exact (section 3.1 point 8).  The
runtime-import text is the idempotence marker: a source that already imports the runtime
module is returned unchanged.

| plan record | injection |
|---|---|
| boundary guard, exported param | `__dv.guardInt/guardIntArray/guardArray/guardUnion("fn", "p", p);` after the function's `{` |
| `@pre` (kind `pre`) | `if (!(TEXT)) throw new __dv.PreconditionError("fn", "TEXT", {params}, "file:line:col");` after the guards |
| `@post` | every `return e;` becomes `return ((result) => { if (!(TEXT)) throw new __dv.PostconditionError("fn", "TEXT", {params, result}, "loc"); return result; })(e);` |
| `index` | `a[i]` → `a[__dv.checkIndex(a, i, "loc")]` (the object text is repeated) |
| `slice` | `a.slice(i, j)` → `a.slice(i, j, __dv.checkSlice(a, i, j, "loc"))` (an extra argument `slice` ignores, so nothing is deleted) |
| `append-length` | `[...a, ...b]` → `__dv.checkLength([...a, ...b], "loc")` |
| `range` | `e` → `__dv.checkRange(e, "loc")` |
| `pre-call` | `f(a)` → `(__dv.checkPre(COND, "f", "PRE-TEXT", "loc"), f(a))`, `COND` = the callee's `@pre` tags with the call's argument texts substituted |
| loop `invariant-*` | at the loop body's `{`: `__dv.checkInvariant(INV, "fn", "INV", "loc");` |
| loop `measure-*` | at the loop body's `{`: `__dv.checkMeasure(M, …)`; a loop whose function is not recursive also gets `__dv.checkMeasureDecrease(M, …)` (a per-source-location monitor: first visit is the initialization, later visits must be strictly smaller — sound because a non-recursive function cannot re-enter its own loop) |
| call `measure-nonneg` | `(__dv.checkMeasure(M', "fn", "@decreases M", "loc"), f(a))`, `M'` = the measure with the call's arguments substituted |
| call `measure-decrease` | `(__dv.checkMeasureDecrease(M', M, "loc"), f(a))` (stateless: `M'` and `M` are both evaluated at the call) |

- **Span widening.** Expression spans exclude grouping parentheses (`2 * (s.w + s.h)` is
  stored as `2 * (s.w + s.h`), so a wrap closes the brackets that belong to the region and
  opens the ones that were closed before it; if that is not possible the injection throws.
- **Nesting.** Insertions form a tree: a point insertion sorts before a wrap at the same
  offset, so `a[i + 1]` becomes `a[__dv.checkIndex(a, __dv.checkRange(i + 1, "…"), "…")]` and
  a `return` of a ternary keeps its range checks inside the postcondition wrapper.
- **Failing loudly.** A plan entry that names no function, points at no such expression, has
  empty spec text or a `return;` without a value throws `InjectionError` with a located
  `internal` diagnostic.  The finished text is also handed to `Bun.Transpiler`; if it no
  longer parses, injection throws instead of letting Bun run half-checked code.
- **Guards.** `guardInt` = safe integer, `guardIntArray` = every element is a safe integer
  (O(n)), `guardArray` = an array within `2^32-1`, `guardUnion` = a non-null object (the
  helper is not told the union's discriminant, so that is the boundary it can check).
- **Errors.** `PreconditionError`/`PostconditionError`/`ObligationError` all carry `fn`,
  `spec`, `args`, `loc` (and `file`/`line`/`col` when the location parses).  Guards and the
  low-level checks are called without a location by design (section 6.6); the injected
  `@pre`/`@post` checks do carry the JSDoc location of the spec they enforce.

## Production stripping (`NODE_ENV=production`)

| record | development | production |
|---|---|---|
| boundary guard of an exported parameter | keep | **keep** |
| `@pre` of an exported function | keep | **keep** |
| `@pre` of a non-exported function called from unverified code in the same file | keep | **keep** |
| `@pre` of a non-exported function whose callers are all verified | keep | drop |
| `@post` (all sites certified) | keep | drop |
| `@post` (uncertified) | keep | **keep** |
| internal obligation (certified) | keep | drop |
| internal obligation (uncertified) | keep | **keep** |

## Cache (`src/cache.ts`)

`.dep-verify/cache/<sha256>.json`.  The key hashes `CACHE_VERSION`, the strict flag, the Z3
timeout, whether a solver was available, the file's content hash and `[path, hash]` of every
file it imports transitively.  The entry is
`{version, key, path, sourceHash, imports, report}` where `report` is `verify()`'s result
without the kernel `env` (`functions`, `diagnostics`, `plan`, `externals`, `axioms`).  A
corrupt entry, a version mismatch, a key mismatch or a `path` mismatch is ignored and then
rewritten; a write failure is ignored.  `verifyCached` returns the report plus
`cached: boolean`.

## CLI (`bun run verify [paths…] [--lenient]`)

Verifies files or directories (default `examples/pass`), strict unless `--lenient`, prints
diagnostics and a table of `certified / smt-only / failed / rejected` with `axioms used`
(which must be 0), checks every `external` declaration against its own file and content hash,
and never injects or runs anything.  Exit codes: `0` verified, `1` any failure (including a
failed obligation under `--lenient` — a counterexample is not something a runtime check can
excuse, whereas `smt-only` and uncertified imports are warnings), `2` usage error.  When
`libz3` is missing, strict errors out before verifying and lenient prints one warning and
reports every obligation as `smt-only` (runtime-checked).

Environment: `DEP_VERIFY_STRICT=1` (strict plugin), `DEP_VERIFY_LIBZ3` (library path),
`DEP_VERIFY_NO_CACHE=1` (bypass the cache), `NODE_ENV=production` (strip).

## Deviation worth knowing

The plugin's `isOwnSource` skips this repository's `src/`, **`test/` and `scripts/`**: test
files mention `@pre` inside strings and fixtures on purpose, and the plugin must not treat
those as specs.
