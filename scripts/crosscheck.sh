#!/usr/bin/env bash
# Run the same spec with TLC and tla2rs and compare state counts, violated invariants, and
# counterexample lengths.
#   scripts/crosscheck.sh examples/DieHard.tla [examples/DieHard.cfg] [-deadlock]
#   scripts/crosscheck.sh examples/DieHard.cfg            (the spec is the cfg name up to the first -)
# For a configuration in examples/ or tests/tlc/, TLC's side is the static result in tests/expected/,
# written by scripts/expected.sh; this script does not run TLC for them. A missing or stale result
# fails the check. For any other configuration it runs TLC.
#   scripts/crosscheck.sh --expected X.cfg        write X's result if missing or stale (expected.sh)
#   scripts/crosscheck.sh --expected-force X.cfg  rewrite it
#   scripts/crosscheck.sh --expected-check X.cfg  rerun TLC and compare with the file, without writing
# Pass tla2tools.jar via TLA_TOOLS (default ~/.tla/tla2tools.jar).
# State counts at a violation depend on search order, so TLC runs with one worker for a fixed order.
set -euo pipefail
mode=compare
case "${1:-}" in --expected|--expected-force|--expected-check) mode="${1#--}"; shift ;; esac
tla="$1"; shift
if [[ "$tla" == *.cfg ]]; then
  cfg="$tla"; base=$(basename "$cfg" .cfg); tla="$(dirname "$cfg")/${base%%-*}.tla"
  [[ -f "$tla" ]] || tla="$(dirname "$cfg")/$base.tla"
else
  cfg="${tla%.tla}.cfg"
  if [[ $# -gt 0 && "$1" == *.cfg ]]; then cfg="$1"; shift; fi
fi
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
cfg_abs="$(cd "$(dirname "$cfg")" && pwd)/$(basename "$cfg")"; cfg_rel="${cfg_abs#"$root"/}"
spec_dir="$(cd "$(dirname "$tla")" && pwd)"
t=$(basename "$tla"); c=$(basename "$cfg")
# The modules of the spec's directory that the spec reads: every module whose name appears as a word
# in the spec or in a module already found (EXTENDS and INSTANCE, also across lines and inside LET).
# A name that appears for another reason only adds a file, which is harmless.
modules=()
local_names=$(cd "$spec_dir" && ls *.tla | sed 's/\.tla$//')
queue=("${t%.tla}")
while [[ ${#queue[@]} -gt 0 ]]; do
  m="${queue[0]}"; queue=("${queue[@]:1}")
  [[ -f "$spec_dir/$m.tla" && " ${modules[*]-} " != *" $m "* ]] || continue
  modules+=("$m")
  for f in $(grep -owF "$local_names" "$spec_dir/$m.tla" | sort -u); do queue+=("$f"); done
done

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

# TLC's result depends only on the jar, the cfg, the arguments and the modules the spec reads
# (followed through EXTENDS and INSTANCE within the spec's directory; standard modules come from the
# jar). For a configuration in examples/ or tests/tlc/, the summary TLC gives (verdict, counts, trace
# length, exit code) is kept in tests/expected/ with a hash of those inputs (the key). The parts of
# TLC's output that vary from run to run (times, the fingerprint seed, the shape of a liveness
# counterexample) are not part of the summary, so the file is the same for every TLC run.
# CROSSCHECK_NO_CACHE=1 builds the checker from scratch instead of reusing target/crosscheck/build.
tlc_key() {
  { echo "v1 -workers 1 ${extra[*]-}"; shasum -a 256 "$jar" | cut -d' ' -f1; cat "$cfg_abs"
    for m in $(printf '%s\n' "${modules[@]}" | sort); do echo "== $m"; cat "$spec_dir/$m.tla"; done; } | shasum -a 256 | cut -d' ' -f1
}
expected=""
case "$cfg_rel" in
  examples/*.cfg) expected="$root/tests/expected/examples/$(basename "$cfg_rel" .cfg).txt" ;;
  tests/tlc/*.cfg) expected="$root/tests/expected/tlc/$(basename "$cfg_rel" .cfg).txt" ;;
esac
key=$(tlc_key)
if [[ -z "${CROSSCHECK_NO_CACHE:-}" ]]; then export TLA2RS_BUILD_CACHE="$root/target/crosscheck/build"; fi

run_tlc() {
  rc_tlc=0
  # A private java.io.tmpdir: TLC processes sharing one fail at random in SANY when run in parallel
  mkdir -p "$work/jtmp"
  java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers 1 -config "$c" ${extra[@]+"${extra[@]}"} "$t" > tlc.out 2>&1 || rc_tlc=$?
  a=$(summarize tlc.out)
}
expected_text() { echo "key $key"; echo "tlc $(grep -m1 -oE 'Version [0-9.]+' tlc.out || true)"; echo "rc $rc_tlc"; echo "$a"; }
fresh=0
[[ -n "$expected" && -f "$expected" && "$(sed -n 1p "$expected")" == "key $key" ]] && fresh=1

if [[ $mode != compare ]]; then
  [[ -n "$expected" ]] || { echo "ERROR $cfg_rel: not in examples/ or tests/tlc/"; exit 1; }
  if [[ $mode == expected && $fresh == 1 ]]; then echo "fresh $cfg_rel"; exit 0; fi
fi
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for m in "${modules[@]}"; do cp "$spec_dir/$m.tla" "$work/"; done
cp "$cfg_abs" "$work/$c"
cd "$work"

if [[ $mode != compare ]]; then
  run_tlc
  if [[ -z "$(echo "$a" | head -1)" ]]; then
    echo "ERROR $cfg_rel: no verdict from TLC (exit $rc_tlc)"; sed 's/^/    tlc: /' tlc.out | grep -vE 'Parsing|Semantic' | head -10
    exit 1
  fi
  if [[ $mode == expected-check ]]; then
    if [[ -f "$expected" ]] && diff -q <(expected_text | sed 1,2d) <(sed 1,2d "$expected") > /dev/null && [[ $fresh == 1 ]]; then
      echo "same $cfg_rel"
    else
      echo "DIFF $cfg_rel"; diff <(sed 1,2d "$expected" 2>/dev/null) <(expected_text | sed 1,2d) | sed 's/^/    /'
      [[ $fresh == 1 ]] || echo "    (the key is stale or the file is missing)"
    fi
    exit 0
  fi
  mkdir -p "$(dirname "$expected")"
  expected_text > "$expected.tmp$$" && mv "$expected.tmp$$" "$expected"
  echo "updated $cfg_rel"; exit 0
fi

s0=$(date +%s.%N)
rc_rs=0; tlc_cached=0
if [[ -n "$expected" ]]; then
  if [[ $fresh == 0 ]]; then
    echo "$t: no TLC result, or a stale one, in ${expected#"$root"/}"
    echo "  STALE: run scripts/expected.sh $cfg_rel"
    exit 1
  fi
  rc_tlc=$(sed -n 3p "$expected" | cut -d' ' -f2); a=$(sed -n '4,$p' "$expected"); tlc_cached=1
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

b=$(summarize rs.out)
# If TLC produced no verdict (e.g. TLC itself failed), don't treat two empty results as a match
if [[ -z "$(echo "$a" | head -1)" ]]; then
  echo "  NO VERDICT from TLC (exit $rc_tlc)"; sed 's/^/    tlc: /' tlc.out 2>/dev/null | grep -vE 'Parsing|Semantic' | head -10
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
