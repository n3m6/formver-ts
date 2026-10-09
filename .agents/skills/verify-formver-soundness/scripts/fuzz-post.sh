#!/usr/bin/env bash
# Run the independent oracle (fuzz-post.ts) in a chosen plugin mode.
#
# Usage: fuzz-post.sh [--with-plugin] <file.ts> [--fn name]... [--count N] [--seed S] [--gen gen.ts] [--json out.json]
#
# Default (raw): runs from an empty directory, so no bunfig.toml preloads the dep-verify plugin
# and the function runs exactly as written. --with-plugin preloads src/preload.ts, so the
# injected runtime checks run too, and a check firing on a precondition-satisfying input is
# reported as an unexpected throw.
#
# Every run is capped at FUZZ_POST_TIMEOUT seconds (default 60), because a non-terminating
# call cannot be interrupted from inside the process. Bun's engine has proper tail calls, so
# endless tail recursion spins forever instead of overflowing the stack.
# Exit: 0 clean, 1 finding, 2 usage error or untestable, 3 timed out (some call never returned).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../../.." && pwd)"
preload=()
mode=raw
if [[ "${1:-}" == "--with-plugin" ]]; then
  preload=(--preload "$REPO/src/preload.ts")
  mode=plugin
  shift
fi
[[ $# -ge 1 ]] || { sed -n "4p" "$0" >&2; exit 2; }
file="$(realpath "$1")"
shift

cwd="${TMPDIR:-/tmp}/formver-fuzz-cwd"
mkdir -p "$cwd"
[[ ! -e "$cwd/bunfig.toml" ]] || { echo "fuzz-post: $cwd must stay empty" >&2; exit 2; }
cd "$cwd"
limit="${FUZZ_POST_TIMEOUT:-60}"
set +e
FUZZ_POST_MODE="$mode" timeout -k 5 "$limit" bun "${preload[@]}" "$HERE/fuzz-post.ts" "$file" "$@"
code=$?
if [[ $code -eq 124 || $code -eq 137 ]]; then
  echo "result: TIMEOUT after ${limit}s (the first function without a summary line never returned on some input)"
  exit 3
fi
exit "$code"
