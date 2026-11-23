#!/usr/bin/env bash
# Checks the library crates of `tla2rs --emit-lib` (see "The checker as a library" in CLAUDE.md):
# for each configuration, the library is written and built with tests/lib/driver.rs, whose graph
# (built by the library's init and next) is compared with TLC's in tests/expected/ by the hashes of
# `tla2rs --graph`; the driver also builds every state again from its values and takes every step
# with a Checker. This script does not run TLC.
#
#   scripts/lib.sh [X.cfg ...]     (default: examples/*.cfg)
#
# A configuration is skipped when TLC reports an error (its graph is the part explored before the
# error), when it has a VIEW or SYMMETRY (conform::Graph refuses those), when TLC's graph has more
# than MAX_STATES states (default 20000: the graph is held in memory), and when --emit-lib refuses
# the spec. JOBS=N builds N libraries at a time (default 2).
set -uo pipefail
cd "$(dirname "$0")/.."
cargo build --release --quiet
one() {
  local cfg="$1" dir base tla exp work n
  dir=$(dirname "$cfg"); base=$(basename "$cfg" .cfg); tla="$dir/${base%%-*}.tla"
  [[ -f "$tla" ]] || tla="$dir/$base.tla"
  exp="tests/expected/$(basename "$dir")/$base.txt"
  [[ -f "$exp" ]] || { echo "skip  $cfg  (no expected result)"; return; }
  grep -q '^No error has been found' "$exp" || { echo "skip  $cfg  (TLC reports an error)"; return; }
  grep -qE '^[[:space:]]*(VIEW|SYMMETRY)' "$cfg" && { echo "skip  $cfg  (VIEW or SYMMETRY)"; return; }
  n=$(awk '$1 == "states" { print $2 }' "$exp")
  [[ -n "$n" && "$n" -le "${MAX_STATES:-20000}" ]] || { echo "skip  $cfg  (${n:-no} states)"; return; }
  work="target/lib/$(basename "$dir")-$base"
  rm -rf "$work/driver/src"; mkdir -p "$work/driver/src"
  if ! target/release/tla2rs "$tla" -config "$cfg" --emit-lib -o "$work/lib" > "$work/emit.log" 2>&1; then
    if grep -q 'emit-lib does not support' "$work/emit.log"; then echo "skip  $cfg  (not supported by --emit-lib)"; else echo "FAIL  $cfg  (emit: $(tail -1 "$work/emit.log"))"; fi
    return
  fi
  [[ -f "$work/lib/Cargo.toml" ]] || { echo "skip  $cfg  (nothing to explore)"; return; }
  local name; name=$(awk -F'"' '/^name/ { print $2; exit }' "$work/lib/Cargo.toml")
  cp tests/lib/driver.rs "$work/driver/src/main.rs"
  printf '[package]\nname = "driver"\nversion = "0.0.0"\nedition = "2021"\n\n[dependencies]\nspec = { path = "../lib", package = "%s" }\n\n[profile.release]\nopt-level = 1\n\n[workspace]\n' "$name" > "$work/driver/Cargo.toml"
  if ! (cd "$work/driver" && cargo build --release --quiet --offline) > "$work/build.log" 2>&1; then
    echo "FAIL  $cfg  (build: see $work/build.log)"; return
  fi
  "$work/driver/target/release/driver" "$work/graph.dot" > "$work/out.log" 2> "$work/run.log"
  # The checker grows a capacity (of sets, sequences, the strings ToString lists) by building
  # itself again; a library has the ones it was written with
  if grep -qE 'grew beyond|strings the checker lists' "$work/out.log" "$work/run.log"; then echo "skip  $cfg  (outgrows a capacity)"; return; fi
  # What the spec prints comes before the driver's line
  local out; out=$(tail -n 1 "$work/out.log")
  if [[ "$out" != ok* ]]; then echo "FAIL  $cfg  ($out; see $work/out.log and run.log)"; return; fi
  if [[ "$(target/release/tla2rs --graph "$work/graph.dot")" != "$(grep -E '^(states|edges) ' "$exp")" ]]; then
    echo "FAIL  $cfg  (the library's graph is not TLC's)"; return
  fi
  echo "ok    $cfg  ${out#ok }"
}
export -f one
log=$(mktemp); trap 'rm -f "$log"' EXIT
cfgs=("$@"); [[ ${#cfgs[@]} -gt 0 ]] || cfgs=(examples/*.cfg)
printf '%s\n' "${cfgs[@]}" | xargs -P "${JOBS:-2}" -I{} bash -c 'one "$@"' _ {} | tee "$log"
echo "total: $(grep -c '^ok' "$log") ok, $(grep -c '^skip' "$log") skipped, $(grep -c '^FAIL' "$log") FAIL"
! grep -q '^FAIL' "$log"
