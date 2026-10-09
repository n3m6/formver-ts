#!/usr/bin/env bash
# Create an isolated verification run directory and print its path.
#
# Usage: new-run.sh [label]
#   RUN=$(.agents/skills/verify-formver/scripts/new-run.sh cli-verify)
#
# Layout:
#   $RUN/scratch/            programs you write or copy for this run (removed by cleanup.sh)
#   $RUN/evidence/           proof artifacts (kept by cleanup.sh)
#   $RUN/evidence/RUN.txt    repo, HEAD, dirty-file count, start time
#   $RUN/cache-before.txt    .dep-verify/cache listing at start (for cache-delta claims)
#   $RUN/pids                append the PID of anything you background: echo $! >> "$RUN/pids"
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
[[ -f "$REPO/src/cli.ts" && -f "$REPO/src/plugin.ts" ]] || {
  echo "new-run: $REPO does not look like the formver-ts checkout" >&2
  exit 2
}

ROOT="${FORMVER_VERIFY_ROOT:-/tmp/formver-verify}"
label="${1:-run}"
label="${label//[^A-Za-z0-9_.-]/-}"
RUN="$ROOT/$(date +%Y%m%d-%H%M%S)-$label-$$"

mkdir -p "$RUN/scratch" "$RUN/evidence"
: > "$RUN/pids"
{ ls "$REPO/.dep-verify/cache" 2>/dev/null || true; } | sort > "$RUN/cache-before.txt"

{
  echo "run: $RUN"
  echo "repo: $REPO"
  echo "head: $(git -C "$REPO" rev-parse --short HEAD 2>/dev/null || echo unknown)"
  echo "dirty files: $(git -C "$REPO" status --porcelain 2>/dev/null | wc -l)"
  echo "bun: $(bun --version 2>/dev/null || echo missing)"
  echo "cache entries at start: $(wc -l < "$RUN/cache-before.txt")"
  echo "started: $(date -Is)"
} > "$RUN/evidence/RUN.txt"

echo "$RUN"
