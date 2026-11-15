#!/usr/bin/env bash
# Write TLC's result for each configuration to tests/expected/, the static results that
# crosscheck.sh and all.sh compare tla2rs against. This is the only script that runs TLC for the
# configurations in this repository.
#   scripts/expected.sh [-force | -check] [X.cfg ...]
#   scripts/expected.sh -corpus [-large] [-force | -check]
# With no cfg, every configuration in examples/ and tests/tlc/. With -corpus, every model selected in
# tests/corpus.txt, into tests/expected/corpus/ (scripts/corpus.sh fetches the corpus); with -corpus
# -large, the models listed as `large` instead, whose TLC runs take up to hours and tens of GB (see
# "Large models" in CLAUDE.md). By default only
# missing files and files whose key (jar, cfg, arguments and the modules the spec reads) no longer
# matches are rewritten, so a second run changes nothing. -force reruns TLC for every file. -check
# reruns TLC and reports any file whose content differs, without writing. JOBS=N runs N at a time
# (default 4, 2 with -corpus and 1 with -large).
# For a cfg with an intent line, it also runs tla2rs and writes its pinned result, X.tla2rs.txt, when
# missing or stale (see "Intentional differences" in CLAUDE.md); -check does not.
set -uo pipefail
# cfg paths are taken from where the script is run, not from the repository root it works in
cfgs=()
for x in "$@"; do
  [[ "$x" == *.cfg && "$x" != /* ]] && x="$PWD/$x"
  cfgs+=("$x")
done
set -- ${cfgs[@]+"${cfgs[@]}"}
cd "$(dirname "$0")/.."
# tla2rs --graph reduces TLC's state graph to the hashes kept in the files
cargo build --release --quiet || exit 1
corpus=0
[[ "${1:-}" == -corpus ]] && { corpus=1; shift; }
large=()
[[ $corpus == 1 && "${1:-}" == -large ]] && { large=(-large); shift; }
mode=--expected
case "${1:-}" in
  -force) mode=--expected-force; shift ;;
  -check) mode=--expected-check; shift ;;
esac
log=$(mktemp); trap 'rm -f "$log"' EXIT
if [[ $corpus == 1 ]]; then
  CORPUS_DIR=$(scripts/corpus.sh -fetch) || exit 1
  export CORPUS_DIR MODE="$mode"
  jobs=2; [[ ${#large[@]} == 0 ]] || jobs=1
  scripts/corpus.sh ${large[@]+"${large[@]}"} -list |
    xargs -P "${JOBS:-$jobs}" -L1 bash -c 'scripts/crosscheck.sh "$MODE" "$CORPUS_DIR/$0" "$CORPUS_DIR/$1"' | tee "$log"
else
  for x in "$@"; do [[ -f "$x" ]] || echo "ERROR $x: no such cfg"; done | tee "$log"
  if [[ $# -gt 0 ]]; then printf '%s\n' "$@"; else printf '%s\n' examples/*.cfg tests/tlc/*.cfg; fi |
    while read -r x; do [[ -f "$x" ]] && echo "$x"; done |
    xargs -P "${JOBS:-4}" -I{} scripts/crosscheck.sh "$mode" {} | tee -a "$log"
fi
summary=$(awk '{n[$1]++} END{for (k in n) printf "%s%s %d", (s++ ? ", " : ""), k, n[k]}' "$log")
echo "total: $summary"
! grep -qE '^(DIFF|ERROR)' "$log"
