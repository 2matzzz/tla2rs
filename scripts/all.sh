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
  scripts/crosscheck.sh "$tla" "$cfg" "$@" | tail -n +2 | grep -q '  MATCH' && echo "ok    $cfg" || echo "FAIL  $cfg"
}
export -f one
# Lines appear as configurations finish, so their order varies with JOBS
log=$(mktemp); trap 'rm -f "$log"' EXIT
printf '%s\n' examples/*.cfg tests/tlc/*.cfg |
  xargs -P "${JOBS:-4}" -I{} bash -c 'one "$@"' _ {} "$@" | tee "$log"
echo "total: $(grep -c '^ok' "$log") ok, $(grep -c '^FAIL' "$log") FAIL"
! grep -q '^FAIL' "$log"
