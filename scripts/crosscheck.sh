#!/usr/bin/env bash
# Run the same spec with TLC and tla2rs and compare state counts, violated invariants, and
# counterexample lengths.
#   scripts/crosscheck.sh examples/DieHard.tla [examples/DieHard.cfg] [-deadlock]
# Pass tla2tools.jar via TLA_TOOLS (default ~/.tla/tla2tools.jar).
# State counts at a violation depend on search order, so TLC runs with one worker for a fixed order.
set -euo pipefail
orig=("$@"); origdir="$PWD"
tla="$1"; shift
cfg="${tla%.tla}.cfg"
if [[ $# -gt 0 && "$1" == *.cfg ]]; then cfg="$1"; shift; fi
# Split arguments into those passed to both TLC and tla2rs and those for tla2rs only
extra=(); rsonly=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -setcap|-seqcap|-memlimit|-tmpdir) rsonly+=("$1" "$2"); shift 2 ;;
    -notrace|-fp128|-metal|-batched) rsonly+=("$1"); shift ;;
    *) extra+=("$1"); shift ;;
  esac
done
# A cfg line like `\* crosscheck: rsargs -memlimit 0` adds those arguments to tla2rs only
if a=$(grep -m1 -oE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*rsargs[[:space:]].*' "$cfg"); then
  read -r -a more <<< "${a#*rsargs}"
  rsonly+=("${more[@]}")
fi
jar="${TLA_TOOLS:-$HOME/.tla/tla2tools.jar}"
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/target/release/tla2rs"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
# The other modules next to the spec too, for EXTENDS (e.g. an MC.tla that extends the spec)
cp "$(dirname "$tla")"/*.tla "$cfg" "$work/"
cd "$work"
t=$(basename "$tla"); c=$(basename "$cfg")

summarize() {
  # Line 1: verdict (ok / violated invariant / deadlock / failed invariant or assumption), line 2:
  # state counts, line 3: trace length
  local f="$1"
  local res
  local span='line [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module [A-Za-z0-9_]+'
  res=$(grep -oE "Invariant [A-Za-z0-9_]+ is violated|Evaluating invariant [A-Za-z0-9_]+ failed|Action property [A-Za-z0-9_]+ is violated|Property [A-Za-z0-9_]+ is violated|Deadlock reached|Temporal propert(y .* is|ies were) violated|Assumption $span is false|Evaluating assumption $span failed|No error has been found" "$f" | head -1 || true)
  # If none of the above matched but there is an Error: line, treat it as an evaluation error.
  # The message may differ from TLC's (TLC can also stop on an internal exception), so compare
  # only the kind (and the exit code below)
  if [[ -z "$res" ]] && grep -qE '^Error:' "$f"; then
    res="Evaluation error"
  fi
  local temporal=0
  if grep -qE 'Temporal propert(y .* is|ies were) violated' "$f"; then
    res="Temporal property violated"; temporal=1
  fi
  local counts
  counts=$(grep -oE '[0-9,]+ states generated, [0-9,]+ distinct states found' "$f" | tail -1 | tr -d ',' || true)
  local trace
  trace=$(grep -cE '^State [0-9]+:' "$f" || true)
  # Don't compare lengths of liveness counterexamples (lassos); one property can have several
  [[ $temporal == 1 ]] && trace=lasso
  printf '%s\n%s\ntrace=%s\n' "$res" "$counts" "$trace"
}

# TLC's result depends only on the jar, the cfg, the arguments and the modules the spec reads, so it
# is kept in target/crosscheck/tlc under a hash of those and reused. CROSSCHECK_NO_CACHE=1 turns
# both caches off. Modules are followed through EXTENDS and INSTANCE within the spec's directory
# (standard modules come from the jar).
cache_root="$root/target/crosscheck"
tlc_key() {
  local seen=() queue=("${t%.tla}") m f
  while [[ ${#queue[@]} -gt 0 ]]; do
    m="${queue[0]}"; queue=("${queue[@]:1}")
    [[ -f "$m.tla" ]] || continue
    [[ " ${seen[*]-} " == *" $m "* ]] && continue
    seen+=("$m")
    for f in $(grep -oE '(EXTENDS|INSTANCE)[[:space:]]+[A-Za-z0-9_, ]+' "$m.tla" | sed -E 's/^(EXTENDS|INSTANCE)//; s/,/ /g'); do
      queue+=("$f")
    done
  done
  { echo "v1 -workers 1 ${extra[*]-}"; shasum -a 256 "$jar" | cut -d' ' -f1; cat "$c"
    for m in $(printf '%s\n' "${seen[@]}" | sort); do echo "== $m"; cat "$m.tla"; done; } | shasum -a 256 | cut -d' ' -f1
}
run_tlc() {
  rc_tlc=0
  # A private java.io.tmpdir: TLC processes sharing one fail at random in SANY when run in parallel
  mkdir -p "$work/jtmp"
  java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers 1 -config "$c" ${extra[@]+"${extra[@]}"} "$t" > tlc.out 2>&1 || rc_tlc=$?
  if [[ -n "$tlc_cache" ]]; then
    rm -rf "$tlc_cache"; mkdir -p "$tlc_cache.tmp$$" && cp tlc.out "$tlc_cache.tmp$$/" && echo "$rc_tlc" > "$tlc_cache.tmp$$/rc" &&
      mv "$tlc_cache.tmp$$" "$tlc_cache" 2>/dev/null || rm -rf "$tlc_cache.tmp$$"
  fi
}
tlc_cache=""; tlc_cached=0
if [[ -z "${CROSSCHECK_NO_CACHE:-}" ]]; then
  tlc_cache="$cache_root/tlc/$(tlc_key)"
  export TLA2RS_BUILD_CACHE="$cache_root/build"
fi

s0=$(date +%s.%N)
rc_tlc=0; rc_rs=0
if [[ -n "$tlc_cache" && -f "$tlc_cache/rc" ]]; then
  cp "$tlc_cache/tlc.out" tlc.out; rc_tlc=$(cat "$tlc_cache/rc"); tlc_cached=1
else
  run_tlc
fi
s1=$(date +%s.%N)
"$bin" "$t" -config "$c" -o "$work/gen" -workers 1 ${extra[@]+"${extra[@]}"} ${rsonly[@]+"${rsonly[@]}"} > rs.out 2> rs.err || rc_rs=$?
s2=$(date +%s.%N)

# With both VIEW and SYMMETRY, TLC may keep states with equal views as distinct (its choice of
# representative depends on the state itself). tla2rs collapses by orbit of the view, so its
# distinct count can be lower than TLC's. In that case compare only the verdict.
verdict_only=0
if grep -qE '^[[:space:]]*VIEW[[:space:]]' "$c" && grep -qE '^[[:space:]]*SYMMETRY[[:space:]]' "$c"; then
  verdict_only=1
fi
# If the cfg says `\* crosscheck: distinct-only`, don't compare generated-state counts.
# TLC counts successors per \/ branch, so in specs where both branches can hold it counts the
# same successor more than once (distinct counts and verdicts still match).
distinct_only=0
if grep -qE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*distinct-only' "$c"; then
  distinct_only=1
fi

a=$(summarize tlc.out); b=$(summarize rs.out)
# If TLC produced no verdict (e.g. TLC itself failed), don't treat two empty results as a match
# A result read from the cache that does not match is checked again with a fresh TLC run, so a
# stale or bad entry never decides a test
retry_fresh() {
  [[ $tlc_cached == 1 ]] || return 0
  rm -rf "$tlc_cache"; cd "$origdir"; rm -rf "$work"; exec "$root/scripts/crosscheck.sh" "${orig[@]}"
}
if [[ -z "$(echo "$a" | head -1)" ]]; then
  retry_fresh
  echo "  NO VERDICT from TLC (exit $rc_tlc)"; sed 's/^/    tlc: /' tlc.out | grep -vE 'Parsing|Semantic' | head -10
  exit 1
fi
# Compare exit codes too: identical verdict strings with different exit paths are not a match.
# 0 / 10 (assumption) / 11 (deadlock) / 12 (safety) / 13 (liveness) / 75 / 76 / 255 are kept as is;
# anything else (parse errors, tla2rs rejecting the spec) is folded into "error". For an evaluation
# error TLC exits with 76 if it is in an invariant, 75 in the initial states, and otherwise 255 for
# a failed arithmetic operation and 75 for the rest
norm() { case "$1" in 0|10|11|12|13|75|76|255) echo "$1" ;; *) echo error ;; esac; }
a="$a
exit=$(norm $rc_tlc)"; b="$b
exit=$(norm $rc_rs)"
# `\* crosscheck: ignore-exit` skips the exit-code comparison, for a case where TLC reports an
# error but exits with 0 (an error in a temporal property on an initial state)
if grep -qE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*ignore-exit' "$c"; then
  a=$(echo "$a" | grep -v '^exit='); b=$(echo "$b" | grep -v '^exit=')
fi
if [[ $verdict_only == 1 ]]; then
  a=$(echo "$a" | head -1); b=$(echo "$b" | head -1)
elif [[ $distinct_only == 1 ]]; then
  a=$(echo "$a" | sed 's/^[0-9]* states generated //'); b=$(echo "$b" | sed 's/^[0-9]* states generated //')
fi
[[ "$a" == "$b" ]] || retry_fresh
note=""; [[ $tlc_cached == 1 ]] && note=" cached"
printf '%-14s TLC %6.2fs%s | tla2rs %6.2fs (incl. build)\n' "$t" "$(echo "$s1 - $s0" | bc)" "$note" "$(echo "$s2 - $s1" | bc)"
if [[ "$a" == "$b" ]]; then
  if [[ $verdict_only == 1 ]]; then
    echo "  MATCH(verdict only; VIEW+SYMMETRY): $(echo "$a" | tr '\n' ' ')"
  elif [[ $distinct_only == 1 ]]; then
    echo "  MATCH(distinct only; TLC counts \\/-duplicates): $(echo "$a" | tr '\n' ' ')"
  else
    echo "  MATCH: $(echo "$a" | tr '\n' ' ')"
  fi
else
  echo "  MISMATCH"; echo "  TLC:    $(echo "$a" | tr '\n' ' ')"; echo "  tla2rs: $(echo "$b" | tr '\n' ' ')"
  sed 's/^/    rs.err: /' rs.err | head -20
  exit 1
fi
