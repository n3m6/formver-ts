# Verdict cache

Every verification (CLI and plugin) is cached in `.dep-verify/cache/<sha256>.json`, so a
repeat run of unchanged code is near-instant. The key covers the file's absolute path and
content hash, the content hashes of its transitive imports, the strict flag, the timeout,
solver availability, and a fingerprint of the verifier's own `src/**/*.ts`. Changing any of
them misses. `DEP_VERIFY_NO_CACHE=1` bypasses the cache in both directions.

## Sub-features

- `cache-write`: a first warm run of a new file adds exactly one entry whose `path` is that file.
- `cache-hit`: a second run of the unchanged file adds no entry and returns in a fraction of the cold time.
- `cache-edit-miss`: editing the file adds a new entry and costs a cold run again.
- `cache-import-miss`: editing an imported file re-verifies the caller and can change its verdict.
- `cache-bypass`: with `DEP_VERIFY_NO_CACHE=1`, no entry is added and every run is cold.

## How to get to it (user POV)

- Any `bun run verify …` without `DEP_VERIFY_NO_CACHE`.
- Any `bun run` / `bun test` / `Bun.build` that loads an annotated file through the plugin.
- `bun run demo` prints `cache hit` next to cached verdicts.

## Driving it with capture.sh

Preconditions:

- `$SK/doctor.sh` reports `doctor: OK` and `$RUN` exists.
- Scratch copies: `mkdir -p "$RUN/scratch/cache" && cp examples/pass/binarySearch.ts examples/pass/clamp.ts examples/pass/useClamp.ts "$RUN/scratch/cache/"`. Because `binarySearch` takes 15–30 s cold, hits and misses are obvious in the timings.
- This run's entries are listed with `comm -13 "$RUN/cache-before.txt" <(ls .dep-verify/cache | sort) | xargs -r -I{} grep -l "\"path\":\"$RUN/" .dep-verify/cache/{}`. Call that list NEW.

- **First run writes.** Run `$SK/capture.sh "$RUN" verdict-cache.cache-write -- bun run verify "$RUN/scratch/cache/binarySearch.ts"`. Exit 0, a `1 0 0 0` row, and a cold duration (seconds) in the log footer. NEW now holds one entry; `grep -o '"path":"[^"]*"' <entry>` shows the scratch path, and its `report.functions` holds `"status":"certified"`.
- **Second run hits.** Rerun the same command (label `.cache-hit`). The output is identical, the duration is well under a second, and NEW still holds one entry.
- **Edit misses.** Append a comment line (`echo '// edited' >> "$RUN/scratch/cache/binarySearch.ts"`) and rerun (label `.cache-edit-miss`). The duration is cold again, and NEW holds two entries with different `sourceHash` values.
- **Import edit misses.** Run `useClamp.ts` warm twice (labels `.cache-import.first` and `.cache-import.hit`) and confirm the second run hits. Then weaken the scratch `clamp.ts` postcondition to `@post lo <= result` and rerun `useClamp.ts` (label `.cache-import-miss`). Exit 1 with `error[post]`. The cache did not serve the stale `certified` verdict. NEW gains an entry for `useClamp.ts` whose `imports` lists a different hash for `clamp.ts`.
- **Bypass.** Count NEW, then run `$SK/capture.sh "$RUN" verdict-cache.cache-bypass -- env DEP_VERIFY_NO_CACHE=1 bun run verify "$RUN/scratch/cache/binarySearch.ts"` twice. Both durations are cold, and NEW has the same count as before.

## Gotchas

- The cache is shared by every checkout user and agent and is never garbage-collected (it
  holds hundreds of entries). Count only entries whose `path` is under your `$RUN`; never
  infer anything from the total. Never delete entries you did not create (`cleanup.sh`
  removes only yours).
- The key includes the absolute path, so a scratch copy never shares an entry with the repo
  file it was copied from. That is why these recipes copy files instead of editing
  `examples/`.
- The strict flag is part of the key. The CLI (strict) and the plugin (lenient by default)
  create separate entries for the same file.
- Any edit under `src/` changes the fingerprint and invalidates every entry. The first run after
  a verifier change is cold even without `DEP_VERIFY_NO_CACHE=1`.
- The Z3 version is not part of the key. After swapping `DEP_VERIFY_LIBZ3`, run cold.
