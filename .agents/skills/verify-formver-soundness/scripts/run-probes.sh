#!/usr/bin/env bash
# Verify the shipped syntax/semantics probes cold in strict mode, check each with the
# independent oracle, and compare against the expectation on each probe's first line.
#
# Usage: run-probes.sh <run-dir> [probe-name...]     (names without .ts; default: all)
#   run-probes.sh "$RUN"
#   run-probes.sh "$RUN" asi-return hex-literal
#
# A probe starts with `// expect: reject` (the program breaks its spec under real JavaScript
# semantics, so certifying it is unsound) or `// expect: certify` (it is correct; rejecting it is
# only incompleteness). The optional line `// oracle: none` marks a defect that fuzzing cannot
# show. If <name>.gen.ts exists next to a probe, it is passed to the oracle as --gen. The oracle
# runs every probe twice: raw, and under the plugin (--with-plugin), where a runtime check firing
# on a valid input counts as a violation (this is how internal-obligation defects show).
#
# Classes (TSV in $RUN/evidence/probes.tsv; logs in $RUN/evidence/probes/):
#   ok             the verdict matches the expectation, and the oracle agrees with the probe's claim
#   incomplete     expect certify, the verifier did not certify (a completeness gap, not a soundness bug)
#   SOUNDNESS-BUG  expect reject, the verifier certified it (or an expect-certify probe certified but the oracle found a violation)
#   SMT-BUG        expect reject, Z3 proved it (smt-only) and the oracle confirms it is wrong
#   INJECTION-BUG  the raw run violates the spec but the plugin run is clean: the injected code
#                  changed what the function returns (the plugin may only add throws)
#   CHECK-PROBE    the oracle contradicts the probe's own claim, so fix the probe before trusting its row
#   CRASH          the verifier exited with neither 0 nor 1, timed out, or reported error[internal]
# Exit 1 if any row is SOUNDNESS-BUG, SMT-BUG, INJECTION-BUG, CHECK-PROBE or CRASH.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../../.." && pwd)"
PROBES="$(cd "$HERE/../probes" && pwd)"
[[ $# -ge 1 ]] || { sed -n '5,7p' "$0" >&2; exit 2; }
RUN="$1"
shift
[[ -d "$RUN/scratch" && -d "$RUN/evidence" ]] || { echo "run-probes: $RUN is not a run directory (new-run.sh)" >&2; exit 2; }

names=("$@")
if [[ ${#names[@]} -eq 0 ]]; then
  while IFS= read -r path; do names+=("$(basename "$path" .ts)"); done \
    < <(find "$PROBES" -maxdepth 1 -name '*.ts' ! -name '*.gen.ts' | sort)
fi

DIR="$RUN/scratch/probes"
LOGS="$RUN/evidence/probes"
TSV="$RUN/evidence/probes.tsv"
mkdir -p "$DIR" "$LOGS"
# oracle_run raw|plugin <file> <log>: prints clean, VIOLATION, HANG or untestable.
oracle_run() {
  local extra=()
  [[ $1 == plugin ]] && extra=(--with-plugin)
  DEP_VERIFY_NO_CACHE=1 FUZZ_POST_TIMEOUT=60 "$HERE/fuzz-post.sh" "${extra[@]}" "$2" --count 500 "${gen[@]}" > "$3" 2>&1
  case $? in
    0) echo clean ;;
    1) echo VIOLATION ;;
    3) echo HANG ;;
    *) echo untestable ;;
  esac
}

printf 'probe\texpect\tverifier\toracle\tclass\n' > "$TSV"
declare -A counts=()

for name in "${names[@]}"; do
  [[ -f "$PROBES/$name.ts" ]] || { echo "run-probes: no probe $PROBES/$name.ts" >&2; exit 2; }
  cp "$PROBES/$name.ts" "$DIR/"
  gen=()
  if [[ -f "$PROBES/$name.gen.ts" ]]; then
    cp "$PROBES/$name.gen.ts" "$DIR/"
    gen=(--gen "$DIR/$name.gen.ts")
  fi
  probe="$DIR/$name.ts"
  expect="$(sed -n '1s#^// expect: \(certify\|reject\).*#\1#p' "$probe")"
  [[ -n "$expect" ]] || { echo "run-probes: $name.ts lacks a first-line '// expect: certify|reject'" >&2; exit 2; }
  oracle_mode=check
  grep -q '^// oracle: none' "$probe" && oracle_mode=none

  vlog="$LOGS/$name.verify.log"
  (cd "$REPO" && DEP_VERIFY_NO_CACHE=1 timeout -k 5 300 bun src/cli.ts "$probe") > "$vlog" 2>&1
  vcode=$?
  read -r c s f r <<< "$(awk -v p="$probe" '$1 == p { print $2, $3, $4, $5 }' "$vlog")"
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

  raw="$(oracle_run raw "$probe" "$LOGS/$name.oracle.log")"
  plugin="$(oracle_run plugin "$probe" "$LOGS/$name.oracle-plugin.log")"
  oracle="raw=$raw plugin=$plugin"
  wrong=no
  [[ "$raw $plugin" =~ VIOLATION|HANG ]] && wrong=yes

  # Plugin mode only adds checks that throw, and both runs see the same inputs (same seed), so
  # a raw violation that disappears under the plugin means injection changed a value.
  injection=no
  [[ ( $raw == VIOLATION || $raw == HANG ) && $plugin == clean ]] && injection=yes

  case "$expect:$verdict:$injection" in
    *:crash*) class=CRASH ;;
    reject:certified:*) class=SOUNDNESS-BUG ;;
    certify:certified:*) if [[ $wrong == yes ]]; then class=SOUNDNESS-BUG; else class=ok; fi ;;
    *:yes) class=INJECTION-BUG ;;
    reject:smt-only:*) if [[ $wrong == yes ]]; then class=SMT-BUG; else class=CHECK-PROBE; fi ;;
    reject:*) if [[ $wrong == yes || $oracle_mode == none ]]; then class=ok; else class=CHECK-PROBE; fi ;;
    certify:*) if [[ $wrong == yes ]]; then class=CHECK-PROBE; else class=incomplete; fi ;;
  esac
  counts[$class]=$(( ${counts[$class]:-0} + 1 ))
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$expect" "$verdict" "$oracle" "$class" >> "$TSV"
  printf '%-22s expect %-8s %-40s %-30s %s\n' "$name" "$expect" "$verdict" "$oracle" "$class"
done

summary=""
for key in "${!counts[@]}"; do summary+="$key=${counts[$key]} "; done
echo "probes: ${summary% }"
echo "table: $TSV"
for bad in SOUNDNESS-BUG SMT-BUG INJECTION-BUG CHECK-PROBE CRASH; do
  [[ ${counts[$bad]:-0} -eq 0 ]] || exit 1
done
