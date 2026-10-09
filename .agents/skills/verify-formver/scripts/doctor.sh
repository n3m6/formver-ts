#!/usr/bin/env bash
# Read-only health check: is this formver-ts checkout worth driving?
#
# Usage: doctor.sh
#
# Checks Bun, the Z3 shared library (honours DEP_VERIFY_LIBZ3), the bunfig preloads, the
# typecheck devDependency, and a cold strict smoke verification of examples/pass/clamp.ts.
# The smoke run uses DEP_VERIFY_NO_CACHE=1, so nothing is written to .dep-verify/.
# Prints one line per check and ends with `doctor: OK` (exit 0) or `doctor: FAILED` (exit 1).
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
EXPECTED_BUN="1.4.2"
problems=0
ok() { echo "  ok    $*"; }
warn() { echo "  warn  $*"; }
bad() { echo "  FAIL  $*"; problems=$((problems + 1)); }

echo "doctor: $REPO"
[[ -f "$REPO/src/cli.ts" && -f "$REPO/src/plugin.ts" ]] || { bad "not the formver-ts checkout"; echo "doctor: FAILED"; exit 1; }
cd "$REPO"

echo "  info  HEAD $(git rev-parse --short HEAD 2>/dev/null || echo '?') on $(git branch --show-current 2>/dev/null || echo '?'), $(git status --porcelain 2>/dev/null | wc -l) dirty file(s)"

bun_version="$(bun --version 2>/dev/null || true)"
if [[ -z "$bun_version" ]]; then
  bad "bun is not on PATH"
elif [[ "$bun_version" == "$EXPECTED_BUN" ]]; then
  ok "bun $bun_version"
else
  warn "bun $bun_version (the repo was built and verified against $EXPECTED_BUN)"
fi

z3_out="$(bun -e 'import * as z3 from "./src/vc/z3"; const v = z3.version(); if (v === undefined) { console.error(z3.unavailableReason()); process.exit(1); } console.log(`${v} from ${z3.libraryPath()}`);' 2>&1)"
if [[ $? -eq 0 ]]; then ok "$z3_out"; else bad "Z3 unavailable: $z3_out (run \`bun run setup\`, or set DEP_VERIFY_LIBZ3)"; fi

preloads=$(grep -c '^[[:space:]]*preload[[:space:]]*=[[:space:]]*\["\./src/preload\.ts"\]' bunfig.toml 2>/dev/null || true)
if [[ "$preloads" == "2" ]]; then
  ok "bunfig.toml preloads src/preload.ts for bun run and bun test"
else
  bad "bunfig.toml should preload ./src/preload.ts twice (top level and [test]); found $preloads"
fi

if [[ -d node_modules/typescript ]]; then
  ok "node_modules/typescript present (bun run typecheck works)"
else
  warn "node_modules/typescript missing: run \`bun install\` before \`bun run typecheck\`"
fi

smoke="$(DEP_VERIFY_NO_CACHE=1 bun src/cli.ts examples/pass/clamp.ts 2>&1)"
code=$?
if [[ $code -eq 0 ]] && grep -Eq '^examples/pass/clamp\.ts +1 +0 +0 +0$' <<< "$smoke" && grep -q '^axioms used: 0$' <<< "$smoke"; then
  ok "cold strict verify of examples/pass/clamp.ts: 1 certified, 0 axioms"
else
  bad "cold strict verify of examples/pass/clamp.ts failed (exit $code):"
  sed 's/^/        /' <<< "$smoke"
fi

entries=$(find .dep-verify/cache -maxdepth 1 -name '*.json' 2>/dev/null | wc -l)
echo "  info  .dep-verify/cache holds $entries entr$([[ $entries == 1 ]] && echo y || echo ies) (shared by every run; never wipe it wholesale)"

if [[ $problems -eq 0 ]]; then
  echo "doctor: OK"
else
  echo "doctor: FAILED ($problems problem(s))"
  exit 1
fi
