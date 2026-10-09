#!/usr/bin/env bash
# Mutate an annotated file, verify every mutant cold in strict mode, run the independent oracle
# on it, and classify the pair.
#
# Usage: run-mutants.sh <run-dir> <file.ts> [--max N] [--count N] [--gen gen.ts]
#   run-mutants.sh "$RUN" examples/pass/clamp.ts
#
# The oracle runs every mutant twice: raw, and under the plugin (--with-plugin), where a
# runtime check firing on a valid input exposes a false internal obligation (pre-call, index,
# range, measure) that the raw result alone can hide.
#
# Classes (one TSV row per mutant in $RUN/evidence/mutants-<name>.tsv):
#   killed              the verifier did not certify it, and an oracle run found a violation
#   killed-oracle-clean the verifier did not certify it, and neither oracle run found anything
#                       (an equivalent mutant, or a gap in completeness or in the oracle's inputs)
#   survived            certified, and neither oracle run found anything (argue why it is equivalent)
#   smt-only            Z3 proved it without a kernel certificate, and neither oracle run found anything
#   SOUNDNESS-BUG       certified, and an oracle run found a concrete violation or a hang
#   SMT-BUG             smt-only, and an oracle run found a concrete violation or a hang
#   INJECTION-BUG       the raw run violates the spec but the plugin run is clean: the injected
#                       code changed what the function returns (the plugin may only add throws)
#   CRASH               the verifier exited with neither 0 nor 1, timed out, or reported error[internal]
# Per-mutant verifier and oracle logs go to $RUN/evidence/mutants-<name>/. Exit 1 if any row is
# SOUNDNESS-BUG, SMT-BUG, INJECTION-BUG or CRASH.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../../.." && pwd)"
[[ $# -ge 2 ]] || { sed -n '5,6p' "$0" >&2; exit 2; }
RUN="$1"
FILE="$(realpath "$2")"
shift 2
MAX=60
COUNT=300
GEN=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --max) MAX="$2"; shift 2 ;;
    --count) COUNT="$2"; shift 2 ;;
    --gen) GEN=(--gen "$(realpath "$2")"); shift 2 ;;
    *) echo "run-mutants: unknown option $1" >&2; exit 2 ;;
  esac
done
[[ -d "$RUN/scratch" && -d "$RUN/evidence" ]] || { echo "run-mutants: $RUN is not a run directory (new-run.sh)" >&2; exit 2; }

name="$(basename "$FILE")"
stem="${name%.*}"
OUT="$RUN/scratch/mutants/$stem"
LOGS="$RUN/evidence/mutants-$stem"
TSV="$RUN/evidence/mutants-$stem.tsv"
# Two runs on the same file in one run directory would share $OUT and interleave $TSV.
exec 9> "$RUN/scratch/.mutants-$stem.lock"
flock -n 9 || { echo "run-mutants: another run-mutants is already working on $stem in $RUN" >&2; exit 2; }
rm -rf "$OUT" "$LOGS"
mkdir -p "$OUT" "$LOGS"
bun "$HERE/mutate.ts" "$FILE" "$OUT" --max "$MAX" > "$LOGS/mutants.txt" || exit 2

# oracle_run raw|plugin <file> <log>: prints clean, VIOLATION, HANG or untestable.
oracle_run() {
  local extra=()
  [[ $1 == plugin ]] && extra=(--with-plugin)
  DEP_VERIFY_NO_CACHE=1 FUZZ_POST_TIMEOUT=60 "$HERE/fuzz-post.sh" "${extra[@]}" "$2" --count "$COUNT" "${GEN[@]}" > "$3" 2>&1
  case $? in
    0) echo clean ;;
    1) echo VIOLATION ;;
    3) echo HANG ;;
    *) echo untestable ;;
  esac
}

printf 'id\tline\toperator\tchange\tverifier\toracle\tclass\n' > "$TSV"
declare -A counts=()
while IFS=$'\t' read -r id line op change; do
  mutant="$OUT/$id/$name"
  vlog="$LOGS/$id.verify.log"
  flog="$LOGS/$id.oracle.log"

  (cd "$REPO" && DEP_VERIFY_NO_CACHE=1 timeout -k 5 300 bun src/cli.ts "$mutant") > "$vlog" 2>&1
  vcode=$?
  read -r c s f r <<< "$(awk -v p="$mutant" '$1 == p { print $2, $3, $4, $5 }' "$vlog")"
  c=${c:-0} s=${s:-0} f=${f:-0} r=${r:-0}
  if [[ $vcode -ne 0 && $vcode -ne 1 ]] || grep -q 'error\[internal\]' "$vlog"; then
    verdict="crash(exit $vcode)"
  elif [[ $vcode -eq 0 && $c -gt 0 && $s -eq 0 && $f -eq 0 && $r -eq 0 ]]; then
    verdict=certified
  elif [[ $s -gt 0 && $f -eq 0 && $r -eq 0 ]]; then
    verdict=smt-only
  else
    kinds="$(grep -o 'error\[[a-z-]*\]' "$vlog" | sort -u | tr '\n' ' ' | sed 's/ $//')"
    verdict="rejected ${kinds:-(exit $vcode, no error line)}"
  fi

  raw="$(oracle_run raw "$mutant" "$flog")"
  plugin="$(oracle_run plugin "$mutant" "$LOGS/$id.oracle-plugin.log")"
  oracle="raw=$raw plugin=$plugin"
  wrong=no
  [[ "$raw $plugin" =~ VIOLATION|HANG ]] && wrong=yes

  # Plugin mode only adds checks that throw, and both runs see the same inputs (same seed), so
  # a raw violation that disappears under the plugin means injection changed a value.
  injection=no
  [[ ( $raw == VIOLATION || $raw == HANG ) && $plugin == clean ]] && injection=yes

  case "$verdict:$wrong:$injection" in
    crash*) class=CRASH ;;
    certified:yes:*) class=SOUNDNESS-BUG ;;
    smt-only:yes:*) class=SMT-BUG ;;
    *:yes) class=INJECTION-BUG ;;
    certified:no:*) class=survived ;;
    smt-only:no:*) class=smt-only ;;
    *:no:*) class=killed-oracle-clean ;;
    *) class=killed ;;
  esac
  counts[$class]=$(( ${counts[$class]:-0} + 1 ))
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$id" "$line" "$op" "$change" "$verdict" "$oracle" "$class" >> "$TSV"
  printf '%s L%-3s %-40s %-28s %-30s %s\n' "$id" "$line" "$op" "$verdict" "$oracle" "$class"
done < "$LOGS/mutants.txt"

summary=""
for key in "${!counts[@]}"; do summary+="$key=${counts[$key]} "; done
echo "mutants of $name: ${summary% }"
echo "table: $TSV"
if [[ ${counts[SOUNDNESS-BUG]:-0} -gt 0 || ${counts[SMT-BUG]:-0} -gt 0 || ${counts[INJECTION-BUG]:-0} -gt 0 || ${counts[CRASH]:-0} -gt 0 ]]; then
  exit 1
fi
