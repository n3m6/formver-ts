#!/usr/bin/env bash
# Tear down one verification run without touching its evidence.
#
# Usage: cleanup.sh <run-dir>
#
# 1. Kills only the PIDs recorded in $RUN/pids (never by process name: the editor, the user's
#    shells and other agents all run `bun`).
# 2. Archives every .ts file under $RUN/scratch to $RUN/evidence/inputs/, so the proof keeps
#    the exact sources that were verified.
# 3. Deletes $RUN/scratch.
# 4. Deletes .dep-verify/cache entries created since new-run.sh whose "path" points into $RUN
#    (they are dead once scratch is gone). Entries for repository files are valid cache and stay.
# Safe to run repeatedly, including after a failed attempt.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
ROOT="${FORMVER_VERIFY_ROOT:-/tmp/formver-verify}"
RUN="${1:-}"
[[ -n "$RUN" ]] || { echo "usage: cleanup.sh <run-dir>" >&2; exit 2; }
RUN="$(cd "$RUN" && pwd)"
case "$RUN" in
  "$ROOT"/*) ;;
  *) echo "cleanup: refusing $RUN (not under $ROOT)" >&2; exit 2 ;;
esac
[[ -f "$RUN/evidence/RUN.txt" ]] || { echo "cleanup: $RUN has no evidence/RUN.txt; not a run directory" >&2; exit 2; }

if [[ -s "$RUN/pids" ]]; then
  while read -r pid; do
    [[ "$pid" =~ ^[0-9]+$ ]] || continue
    if kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
      echo "[cleanup] killed $pid"
    fi
  done < "$RUN/pids"
  : > "$RUN/pids"
fi

if [[ -d "$RUN/scratch" ]]; then
  archived=0
  while IFS= read -r -d '' file; do
    rel="${file#"$RUN/scratch/"}"
    mkdir -p "$RUN/evidence/inputs/$(dirname "$rel")"
    cp "$file" "$RUN/evidence/inputs/$rel"
    archived=$((archived + 1))
  done < <(find "$RUN/scratch" -type f \( -name '*.ts' -o -name '*.mts' -o -name 'MUTATION.txt' \) -print0)
  rm -rf "$RUN/scratch"
  echo "[cleanup] archived $archived input file(s) to $RUN/evidence/inputs, removed scratch/"
fi

CACHE="$REPO/.dep-verify/cache"
removed=0
if [[ -d "$CACHE" && -f "$RUN/cache-before.txt" ]]; then
  while IFS= read -r entry; do
    [[ -n "$entry" ]] || continue
    if grep -qF "\"path\":\"$RUN/" "$CACHE/$entry" 2>/dev/null; then
      rm -f "$CACHE/$entry"
      removed=$((removed + 1))
    fi
  done < <(comm -13 "$RUN/cache-before.txt" <(ls "$CACHE" | sort))
fi
echo "[cleanup] removed $removed cache entr$([[ $removed == 1 ]] && echo y || echo ies) pointing into this run"

echo "cleaned: $(date -Is)" >> "$RUN/evidence/RUN.txt"
echo "[cleanup] evidence kept at $RUN/evidence:"
find "$RUN/evidence" -maxdepth 1 -mindepth 1 -printf '  %f\n' | sort
