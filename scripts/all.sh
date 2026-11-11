#!/usr/bin/env bash
# Cross-check every configuration in examples/ and tests/tlc/ against TLC.
# Extra arguments (e.g. -batched, -metal) are passed on to every crosscheck.sh run
set -uo pipefail
cd "$(dirname "$0")/.."
cargo build --release --quiet
fail=0
for cfg in examples/*.cfg tests/tlc/*.cfg; do
  dir=$(dirname "$cfg"); base=$(basename "$cfg" .cfg); tla="$dir/${base%%-*}.tla"
  [[ -f "$tla" ]] || tla="$dir/$base.tla"
  scripts/crosscheck.sh "$tla" "$cfg" "$@" | tail -n +2 | grep -q '  MATCH' && echo "ok    $cfg" || { echo "FAIL  $cfg"; fail=1; }
done
exit $fail
