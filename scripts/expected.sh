#!/usr/bin/env bash
# Write TLC's result for each configuration to tests/expected/, the static results that
# crosscheck.sh and all.sh compare tla2rs against. This is the only script that runs TLC for the
# configurations in this repository.
#   scripts/expected.sh [-force | -check] [X.cfg ...]
# With no cfg, every configuration in examples/ and tests/tlc/. By default only missing files and
# files whose key (jar, cfg, arguments and the modules the spec reads) no longer matches are
# rewritten, so a second run changes nothing. -force reruns TLC for every file. -check reruns TLC
# and reports any file whose content differs, without writing. JOBS=N runs N at a time (default 4).
set -uo pipefail
cd "$(dirname "$0")/.."
mode=--expected
case "${1:-}" in
  -force) mode=--expected-force; shift ;;
  -check) mode=--expected-check; shift ;;
esac
log=$(mktemp); trap 'rm -f "$log"' EXIT
if [[ $# -gt 0 ]]; then printf '%s\n' "$@"; else printf '%s\n' examples/*.cfg tests/tlc/*.cfg; fi |
  xargs -P "${JOBS:-4}" -I{} scripts/crosscheck.sh "$mode" {} | tee "$log"
summary=$(awk '{n[$1]++} END{for (k in n) printf "%s%s %d", (s++ ? ", " : ""), k, n[k]}' "$log")
echo "total: $summary"
! grep -qE '^(DIFF|ERROR)' "$log"
