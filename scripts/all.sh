#!/usr/bin/env bash
# Cross-check every configuration in examples/ and tests/tlc/ against TLC's results in
# tests/expected/ (written by scripts/expected.sh; this script does not run TLC).
# Extra arguments (e.g. -batched, -metal) are passed on to every crosscheck.sh run; arguments that
# name .cfg files check those configurations only.
# JOBS=N runs N configurations at a time (default 4; JOBS=1 runs them one by one). Each checker
# uses one worker, so the results do not depend on JOBS.
set -uo pipefail
cd "$(dirname "$0")/.."
cargo build --release --quiet
one() {
  local cfg="$1"; shift
  local dir base tla
  dir=$(dirname "$cfg"); base=$(basename "$cfg" .cfg); tla="$dir/${base%%-*}.tla"
  [[ -f "$tla" ]] || tla="$dir/$base.tla"
  local out
  out=$(scripts/crosscheck.sh "$tla" "$cfg" "$@" 2>&1)
  if tail -n +2 <<< "$out" | grep -q '  MATCH'; then
    # A comparison narrowed by a rule says which, as in MATCH(verdict only; ...)
    echo "ok    $cfg$(grep -oE '  MATCH\([^)]*\)' <<< "$out" | sed 's/  MATCH/  /')"
  elif tail -n +2 <<< "$out" | grep -q '  INTENT('; then
    # An intentional difference matched its pinned result (see "Intentional differences" in CLAUDE.md)
    echo "intent $cfg$(grep -oE '  INTENT\([^)]*\)' <<< "$out" | sed 's/  INTENT/  /')"
  elif tail -n +2 <<< "$out" | grep -q '  AGREES('; then
    echo "agrees $cfg$(grep -oE '  AGREES\([^)]*\)' <<< "$out" | sed 's/  AGREES/  /')"
  else
    # Keep the details of a failure, since the summary line alone does not say what differed
    mkdir -p target/crosscheck/fail && echo "$out" > "target/crosscheck/fail/$(basename "$cfg" .cfg).log"
    echo "FAIL  $cfg"
  fi
}
export -f one
# Lines appear as configurations finish, so their order varies with JOBS
log=$(mktemp); trap 'rm -f "$log"' EXIT
rm -rf target/crosscheck/fail
cfgs=(); args=()
for x in "$@"; do if [[ "$x" == *.cfg ]]; then cfgs+=("$x"); else args+=("$x"); fi; done
[[ ${#cfgs[@]} -gt 0 ]] || cfgs=(examples/*.cfg tests/tlc/*.cfg)
set -- ${args[@]+"${args[@]}"}
printf '%s\n' "${cfgs[@]}" |
  xargs -P "${JOBS:-4}" -I{} bash -c 'one "$@"' _ {} "$@" | tee "$log"
echo "total: $(grep -c '^ok' "$log") ok, $(grep -c '^intent' "$log") intentional differences, $(grep -c '^agrees' "$log") intentional differences TLC now agrees with, $(grep -c '^FAIL' "$log") FAIL"
! grep -q '^FAIL' "$log"
