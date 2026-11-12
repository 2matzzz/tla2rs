#!/usr/bin/env bash
# Cross-check tla2rs against the models of a public corpus of TLA+ specifications, the tlaplus/Examples
# repository, at the commit pinned in tests/corpus.txt. The corpus is fetched into target/corpus/<commit>/
# and never into the tracked tree; its files are only read by TLC and tla2rs. TLC's result for each
# selected model is committed in tests/expected/corpus/ (written by `scripts/expected.sh -corpus`), and
# this script compares against those files only, as all.sh does for the configurations of the repository.
#   scripts/corpus.sh [args ...]   cross-check every selected model (args go to every crosscheck.sh run)
#   scripts/corpus.sh -fetch       fetch the corpus if needed and print its directory
#   scripts/corpus.sh -list        print "<module> <model> <rules> <rsargs>" for every selected model
# tests/corpus.txt lists every model of the corpus's manifests: `check` (selected, must match), `gap`
# (selected, a known difference whose reason is given; reported, not a failure; `norun` if too costly to
# run until it is fixed), or `skip` (not selected, with the reason). A `rules=a,b` field passes narrowing
# rules to crosscheck.sh, and `rsargs=-seqcap,8` arguments to tla2rs only, as the `\* crosscheck:` lines
# of a cfg in the repository do.
# JOBS=N runs N models at a time (default 2: the models are larger than the repository's, and each one
# builds a checker), and each build uses at most CARGO_BUILD_JOBS jobs (default 2).
set -uo pipefail
cd "$(dirname "$0")/.."
root=$(pwd)
list=tests/corpus.txt
url=$(awk '$1 == "url" {print $2}' "$list")
commit=$(awk '$1 == "commit" {print $2}' "$list")
dir="$root/target/corpus/$commit"

fetch() {
  [[ -f "$dir/.fetched" ]] && return 0
  rm -rf "$dir" && mkdir -p "$dir" || return 1
  # A shallow fetch of exactly the pinned commit; nothing in it is run
  git -C "$dir" init -q && git -C "$dir" fetch -q --depth 1 "$url" "$commit" &&
    git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD || { echo "corpus: fetching $url at $commit failed" >&2; return 1; }
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$commit" ]] || { echo "corpus: fetched the wrong commit" >&2; return 1; }
  touch "$dir/.fetched"
}
# Selected models: "<status> <module> <model> <rules> <rsargs>" ("-" for none), paths inside the corpus
selected() {
  awk '($1 == "check" || ($1 == "gap" && $4 != "norun")) {r = "-"; a = "-"; for (i = 4; i <= NF && $i != "#"; i++) { if ($i ~ /^rules=/) r = substr($i, 7); if ($i ~ /^rsargs=/) a = substr($i, 8) }; print $1, $2, $3, r, a}' "$list"
}

case "${1:-}" in
  -fetch) fetch && echo "$dir"; exit ;;
  -list) selected | cut -d' ' -f2-; exit ;;
esac
fetch || exit 1
cargo build --release --quiet || exit 1
one() {
  local status="$1" tla="$2" cfg="$3" rules="$4" rsargs="$5"; shift 5
  local out note
  [[ "$rules" == - ]] && rules=""
  [[ "$rsargs" == - ]] && rsargs=""
  out=$(CROSSCHECK_RULES="${rules//,/ }" CROSSCHECK_RSARGS="${rsargs//,/ }" scripts/crosscheck.sh "$CORPUS_DIR/$tla" "$CORPUS_DIR/$cfg" "$@" 2>&1)
  if tail -n +2 <<< "$out" | grep -q '  MATCH'; then
    note=$(grep -oE '  MATCH\([^)]*\)' <<< "$out" | sed 's/  MATCH/  /')
    if [[ $status == gap ]]; then echo "fixed $cfg$note (listed as a gap)"; else echo "ok    $cfg$note"; fi
  else
    # Keep the details, since the summary line alone does not say what differed
    mkdir -p target/corpus/fail && echo "$out" > "target/corpus/fail/$(echo "$cfg" | tr / _).log"
    if [[ $status == gap ]]; then echo "gap   $cfg"; else echo "FAIL  $cfg"; fi
  fi
}
export -f one
export CORPUS_DIR="$dir" CORPUS_ARGS="$*" CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-2}"
log=$(mktemp); trap 'rm -f "$log"' EXIT
rm -rf target/corpus/fail
selected | xargs -P "${JOBS:-2}" -L1 bash -c 'one "$@" $CORPUS_ARGS' _ | tee "$log"
echo "total: $(grep -c '^ok' "$log") ok, $(grep -c '^gap' "$log") known gaps, $(grep -c '^fixed' "$log") gaps that now match, $(grep -c '^FAIL' "$log") FAIL"
! grep -q '^FAIL' "$log"
