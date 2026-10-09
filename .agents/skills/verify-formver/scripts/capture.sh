#!/usr/bin/env bash
# Run one command and keep its full transcript as evidence.
#
# Usage: capture.sh <run-dir> <label> [--cwd DIR] -- <command> [args...]
#   capture.sh "$RUN" verify-pass -- env DEP_VERIFY_NO_CACHE=1 bun run verify examples/pass
#   capture.sh "$RUN" raw-main --cwd "$RUN/scratch" -- bun main.ts
#
# Writes $RUN/evidence/NN-<label>.log with the command, cwd, every DEP_VERIFY_* / NODE_ENV
# variable in effect, stdout, stderr, exit code and duration; prints the log; and exits with
# the command's own exit code (append `|| true` when a failure is the expected outcome).
# The default cwd is the repo root, where bunfig.toml preloads the dep-verify plugin.
set -uo pipefail

usage() {
  sed -n '2,12p' "$0" >&2
  exit 2
}

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
[[ $# -ge 3 ]] || usage
RUN="$1"
LABEL="${2//[^A-Za-z0-9_.-]/-}"
shift 2
[[ -d "$RUN/evidence" ]] || { echo "capture: $RUN/evidence does not exist (run new-run.sh first)" >&2; exit 2; }

CWD="$REPO"
if [[ "${1:-}" == "--cwd" ]]; then
  CWD="$2"
  shift 2
fi
[[ "${1:-}" == "--" ]] || usage
shift
[[ $# -ge 1 ]] || usage

last=$(find "$RUN/evidence" -maxdepth 1 -name '[0-9][0-9]*-*.log' -printf '%f\n' | sed 's/-.*//' | sort -n | tail -1)
LOG="$RUN/evidence/$(printf '%02d' $((10#${last:-0} + 1)))-$LABEL.log"
out=$(mktemp)
err=$(mktemp)

start=$(date +%s.%N)
(cd "$CWD" && "$@") >"$out" 2>"$err"
code=$?
end=$(date +%s.%N)
duration=$(awk -v a="$start" -v b="$end" 'BEGIN { printf "%.2f", b - a }')

# `env X=1 cmd` sets variables only for the child, so record those from the argv as well.
child_env=()
for arg in "$@"; do
  [[ "$arg" == "env" ]] && continue
  if [[ "$arg" =~ ^(DEP_VERIFY_[A-Z0-9_]+|NODE_ENV)= ]]; then child_env+=("$arg"); else break; fi
done

{
  printf '$'
  printf ' %q' "$@"
  printf '\n'
  echo "cwd: $CWD"
  { env | grep -E '^(DEP_VERIFY_[A-Z0-9_]+|NODE_ENV)=' || true; printf '%s\n' "${child_env[@]}"; } \
    | grep -v '^$' | sort -u | sed 's/^/env: /'
  echo "started: $(date -Is -d "@${start%.*}")"
  echo "--- stdout ---"
  cat "$out"
  echo "--- stderr ---"
  cat "$err"
  echo "--- exit $code after ${duration}s ---"
} > "$LOG"

rm -f "$out" "$err"
cat "$LOG"
echo "[capture] saved $LOG"
exit "$code"
