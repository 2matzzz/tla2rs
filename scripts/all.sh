#!/usr/bin/env bash
# Cross-check every configuration in examples/ and tests/tlc/ against TLC.
# Extra arguments (e.g. -batched, -metal) are passed on to every crosscheck.sh run.
# JOBS=N runs N configurations at a time (default 4; JOBS=1 runs them one by one). TLC and each
# checker use one worker, so the results do not depend on JOBS.
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
    echo "ok    $cfg"
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
printf '%s\n' examples/*.cfg tests/tlc/*.cfg |
  xargs -P "${JOBS:-4}" -I{} bash -c 'one "$@"' _ {} "$@" | tee "$log"
echo "total: $(grep -c '^ok' "$log") ok, $(grep -c '^FAIL' "$log") FAIL"
! grep -q '^FAIL' "$log"
