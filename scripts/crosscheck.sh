#!/usr/bin/env bash
# Run the same spec with TLC and tla2rs and compare state counts, violated invariants,
# counterexamples, exit codes, state graphs, and the messages and printed lines (see "State graphs",
# "Counterexamples" and "Messages and printed lines" in CLAUDE.md).
#   scripts/crosscheck.sh examples/DieHard.tla [examples/DieHard.cfg] [-deadlock]
#   scripts/crosscheck.sh examples/DieHard.cfg            (the spec is the cfg name up to the first -)
# For a configuration in examples/ or tests/tlc/, TLC's side is the static result in tests/expected/,
# written by scripts/expected.sh; this script does not run TLC for them. A missing or stale result
# fails the check. For any other configuration it runs TLC.
#   scripts/crosscheck.sh --expected X.cfg        write X's result if missing or stale (expected.sh)
#   scripts/crosscheck.sh --expected-force X.cfg  rewrite it
#   scripts/crosscheck.sh --expected-check X.cfg  rerun TLC and compare with the file, without writing
#   scripts/crosscheck.sh --expected-from TLC.OUT RC X.cfg
#                                write X's result from the output and exit code of a TLC run done before
#                                (only for a corpus model listed as `large`; see "Large models" in CLAUDE.md)
# For a corpus model listed as `large` in tests/corpus.txt, TLC runs without -dump and tla2rs without
# -dumpgraph, and the state graph is not compared: everything else is.
# Pass tla2tools.jar via TLA_TOOLS (default ~/.tla/tla2tools.jar).
# State counts at a violation depend on search order, so TLC runs with one worker for a fixed order.
set -euo pipefail
mode=compare
case "${1:-}" in
  --expected|--expected-force|--expected-check) mode="${1#--}"; shift ;;
  --expected-from)
    mode=expected-from; [[ $# -ge 4 && -f "$2" && "$3" =~ ^[0-9]+$ ]] || { echo "usage: crosscheck.sh --expected-from TLC.OUT RC X.cfg" >&2; exit 1; }
    from_out="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"; from_rc="$3"; shift 3 ;;
esac
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
# A narrowing rule (`distinct-only`, `ignore-exit`, `error-lines`) applies when the cfg has a line
# `\* crosscheck: <rule>`, or when CROSSCHECK_RULES names it (scripts/corpus.sh passes the rules of
# tests/corpus.txt this way, since the corpus's cfgs are not edited)
has_rule() {
  grep -qE "^[[:space:]]*\\\\\*[[:space:]]*crosscheck:[[:space:]]*$1" "$cfg_abs" || [[ " ${CROSSCHECK_RULES:-} " == *" $1 "* ]]
}
# A cfg line like `\* crosscheck: rsargs -memlimit 0` adds those arguments to tla2rs only
if a=$(grep -m1 -oE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*rsargs[[:space:]].*' "$cfg"); then
  read -r -a more <<< "${a#*rsargs}"
  rsonly+=("${more[@]}")
fi
# A cfg line like `\* crosscheck: args -continue` passes those of TLC's options to both TLC and
# tla2rs (see "TLC's options" in README.md)
if a=$(grep -m1 -oE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*args[[:space:]].*' "$cfg"); then
  read -r -a more <<< "${a#*args}"
  extra+=("${more[@]}")
fi
# With TLC's `-dump [dot,...] FILE`, that file is compared instead of the state graph (TLC writes
# only one dump), and with `-view` the counterexample is read as TLC prints it then (see
# src/options.rs). TLC adds the extension .dump or .dot when the name lacks it. With `-userFile
# FILE`, what the spec prints goes to that file, and the file is compared too (its lines and their
# hash)
user_dump=""; view=0; user_file=""
for ((k = 0; k < ${#extra[@]}; k++)); do
  case "${extra[k]}" in
    -view) view=1 ;;
    -userFile) user_file="${extra[k + 1]:-}" ;;
    -dump)
      v="${extra[k + 1]:-}"
      if [[ "$v" == dot || "$v" == dot,* ]]; then user_dump="${extra[k + 2]:-}"; [[ "$user_dump" == *.dot ]] || user_dump="$user_dump.dot"
      else user_dump="$v"; [[ "$user_dump" == *.dump ]] || user_dump="$user_dump.dump"; fi ;;
  esac
done
# CROSSCHECK_RSARGS does the same (scripts/corpus.sh passes the rsargs= of tests/corpus.txt this way)
if [[ -n "${CROSSCHECK_RSARGS:-}" ]]; then
  read -r -a more <<< "$CROSSCHECK_RSARGS"
  rsonly+=("${more[@]}")
fi
# TLC runs with `-fp 0` (the first fingerprint polynomial) unless the cfg's args choose one, so that
# a liveness counterexample, which depends on TLC's fingerprints, is the same on every run (see
# "Counterexamples" in CLAUDE.md); the checker computes TLC's fingerprints with that polynomial
fp0=(-fp 0)
for x in ${extra[@]+"${extra[@]}"}; do [[ "$x" != -fp ]] || fp0=(); done
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
# The CommunityModules (https://github.com/tlaplus/CommunityModules), for a spec that names one of
# them in EXTENDS or INSTANCE without a module of that name next to it. TLC reads them from the
# release jar given by COMMUNITY_MODULES (default ~/.tla/CommunityModules-deps.jar), which must be
# the release pinned here. TLC 2.19 cannot load the jar's Java overrides of their operators (they
# need classes TLC 2.19 does not have: `NoClassDefFoundError: tlc2/value/impl/KSubsetValue` for
# every spec, measured with the releases from 2023-12 to 2026-11), so it gets the jar's modules only, extracted
# into target/community/<sha256>/, and evaluates their TLA+ definitions. tla2rs does not read them
# (see src/community.rs)
cm_version=202611060952
cm_sha256=a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb
cm_names="BagsExt Bitwise CBOR CSV Combinatorics DifferentialEquations DyadicRationals FiniteSetsExt Folds Functions GraphViz Graphs HTML IOUtils Json Quorum Relation SVG SequencesExt ShiViz Statistics UndirectedGraphs VectorClocks"
uses_cm=0
for m in ${modules[@]+"${modules[@]}"}; do
  for n in $(tr '\n' ' ' < "$spec_dir/$m.tla" | grep -oE '(EXTENDS|INSTANCE)[[:space:]]+[A-Za-z0-9_]+([[:space:]]*,[[:space:]]*[A-Za-z0-9_]+)*' | sed -E 's/^(EXTENDS|INSTANCE)//' | tr ',' ' '); do
    if [[ " $cm_names " == *" $n "* && ! -f "$spec_dir/$n.tla" ]]; then uses_cm=1; fi
  done
done

summarize() {
  # Line 1: verdict (ok / violated invariant / deadlock / failed invariant or assumption), line 2:
  # state counts (generated, distinct, left on queue), line 3: the counterexample (its length and a hash of its states and actions; see
  # src/trace.rs)
  local f="$1"
  local res
  local span='line [0-9]+, col [0-9]+ to line [0-9]+, col [0-9]+ of module [A-Za-z0-9_]+'
  res=$(grep -oE "Invariant [A-Za-z0-9_]+ is violated|Evaluating invariant [A-Za-z0-9_]+ failed|Action property [A-Za-z0-9_]+ is violated|Property [A-Za-z0-9_]+ is violated|Deadlock reached|Temporal propert(y .* is|ies were) violated|Assumption $span is false|Evaluating assumption $span failed|No error has been found" "$f" | head -1 || true)
  # If none of the above matched but there is an Error: line, treat it as an evaluation error. The
  # message itself is compared with the other messages (see messages below)
  if [[ -z "$res" ]] && grep -qE '^Error:' "$f"; then
    res="Evaluation error"
  fi
  if grep -qE 'Temporal propert(y .* is|ies were) violated' "$f"; then
    res="Temporal property violated"
  fi
  # The states left on queue are those of TLC's queue when it stops (0 when the search ends); with
  # one worker they are deterministic (see "Messages and printed lines" in CLAUDE.md)
  local counts
  counts=$(grep -oE '[0-9,]+ states generated, [0-9,]+ distinct states found(, [0-9,]+ states left on queue)?' "$f" | tail -1 | tr -d ',' || true)
  local trace mode=--trace
  [[ $view == 0 ]] || mode=--trace-view
  trace=$("$bin" $mode "$f" || echo "trace unreadable")
  printf '%s\n%s\n%s\n' "$res" "$counts" "$trace"
}

# TLC's result depends only on the jar, the cfg, the arguments and the modules the spec reads
# (followed through EXTENDS and INSTANCE within the spec's directory; standard modules come from the
# jar). For a configuration in examples/ or tests/tlc/, the summary TLC gives (verdict, counts, the
# length and a hash of its counterexample, exit code, hashes of its state graph and of its messages)
# is kept in tests/expected/ with a hash of those inputs and of src/graph.rs, src/trace.rs and
# src/messages.rs, which reduce the graph, the counterexample and the messages to their hashes (the
# key). The parts of TLC's output that vary from run to run (times, the fingerprint seed, temporary
# paths) are not part of the summary, so the file is the same for every TLC run. TLC runs with
# `-fp 0`, so that its liveness counterexample, which depends on its fingerprints, is the same on
# every run too (see "Counterexamples" in CLAUDE.md). A large model's summary has no state graph, so
# its key has no -dump and no src/graph.rs.
# CROSSCHECK_NO_CACHE=1 builds the checker from scratch instead of reusing target/crosscheck/build.
tlc_key() {
  { if [[ $large == 1 ]]; then
      echo "v6 large -workers 1 ${fp0[*]-} ${extra[*]-}"; shasum -a 256 "$jar" "$root/src/trace.rs" "$root/src/messages.rs" | cut -d' ' -f1
    else
      echo "v6 -workers 1 ${fp0[*]-} -dump dot ${extra[*]-}"; shasum -a 256 "$jar" "$root/src/graph.rs" "$root/src/trace.rs" "$root/src/messages.rs" | cut -d' ' -f1
    fi
    cat "$cfg_abs"
    [[ $uses_cm == 0 ]] || echo "community $cm_sha256"
    [[ -z "$user_dump" && $view == 0 ]] || shasum -a 256 "$root/src/options.rs" | cut -d' ' -f1
    for m in $(printf '%s\n' "${modules[@]}" | sort); do echo "== $m"; cat "$spec_dir/$m.tla"; done; } | shasum -a 256 | cut -d' ' -f1
}
expected=""
case "$cfg_rel" in
  examples/*.cfg) expected="$root/tests/expected/examples/$(basename "$cfg_rel" .cfg).txt" ;;
  tests/tlc/*.cfg) expected="$root/tests/expected/tlc/$(basename "$cfg_rel" .cfg).txt" ;;
  # A model of the corpus fetched by scripts/corpus.sh, by its path in the corpus
  target/corpus/*/specifications/*.cfg) p="${cfg_rel#target/corpus/*/specifications/}"; expected="$root/tests/expected/corpus/${p%.cfg}.txt" ;;
esac
# A corpus model listed as `large` in tests/corpus.txt: TLC takes minutes to hours on it, and its state
# graph is too big to write and compare
large=0
if [[ -n "${p:-}" ]] && awk -v m="specifications/$p" '$1 == "large" && $3 == m {f = 1} END {exit !f}' "$root/tests/corpus.txt"; then
  large=1
fi
key=$(tlc_key)
if [[ -z "${CROSSCHECK_NO_CACHE:-}" ]]; then export TLA2RS_BUILD_CACHE="$root/target/crosscheck/build"; fi

# TLC's class path: the jar, and the CommunityModules' modules for a spec that uses them (set by
# set_tlc_cp before TLC runs, so that comparing against tests/expected/ does not need their jar)
tlc_cp="$jar"
set_tlc_cp() {
  [[ $uses_cm == 1 ]] || return 0
  local d; d=$(community_dir) || exit 1
  tlc_cp="$jar:$d"
}
community_dir() {
  local cmjar="${COMMUNITY_MODULES:-$HOME/.tla/CommunityModules-deps.jar}" dir="$root/target/community/$cm_sha256"
  if [[ ! -f "$dir/.extracted" ]]; then
    [[ -f "$cmjar" ]] || { echo "ERROR $cfg_rel: needs the CommunityModules release $cm_version: download CommunityModules-deps-$cm_version.jar to $cmjar (or set COMMUNITY_MODULES)" >&2; return 1; }
    [[ "$(shasum -a 256 "$cmjar" | cut -d' ' -f1)" == "$cm_sha256" ]] || { echo "ERROR $cfg_rel: $cmjar is not CommunityModules-deps-$cm_version.jar (sha256 $cm_sha256)" >&2; return 1; }
    # Into a directory of its own first, as several checks may extract at once
    local tmp="$dir.tmp$$"
    rm -rf "$tmp" && mkdir -p "$tmp" && unzip -q -o "$cmjar" '*.tla' -d "$tmp" && touch "$tmp/.extracted" || return 1
    if [[ -d "$dir" ]]; then rm -rf "$tmp"; else mv "$tmp" "$dir" 2> /dev/null; fi
    rm -rf "$tmp" "$dir/$(basename "$tmp")"
    [[ -f "$dir/.extracted" ]] || return 1
  fi
  echo "$dir"
}
run_tlc() {
  rc_tlc=0
  set_tlc_cp
  # A private java.io.tmpdir: TLC processes sharing one fail at random in SANY when run in parallel
  mkdir -p "$work/jtmp"
  local dump=(-dump dot tlc.dot)
  [[ -z "$user_dump" && $large == 0 ]] || dump=()
  java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$tlc_cp" tlc2.TLC -workers 1 ${fp0[@]+"${fp0[@]}"} ${dump[@]+"${dump[@]}"} -config "$c" ${extra[@]+"${extra[@]}"} "$t" > tlc.out 2>&1 || rc_tlc=$?
  [[ -z "$user_dump" ]] || mv "$user_dump" tlc.userdump 2> /dev/null || true
  [[ -z "$user_file" ]] || mv "$user_file" tlc.userfile 2> /dev/null || true
  a=$(result tlc)
}
# The summary of tlc.out or rs.out (and of its graph), as kept in tests/expected/
result() {
  if [[ $large == 1 ]]; then
    printf '%s\n%s\n' "$(summarize "$1.out")" "$(messages "$1.out")"
  else
    printf '%s\n%s\n%s\n' "$(summarize "$1.out")" "$(graphs "$1")" "$(messages "$1.out")"
  fi
  if [[ -n "$user_file" ]]; then
    if [[ -f "$1.userfile" ]]; then echo "userfile $(wc -l < "$1.userfile" | tr -d ' ') $(shasum -a 256 < "$1.userfile" | cut -d' ' -f1)"; else echo "userfile missing"; fi
  fi
}
# The state graph reduced to hashes of its states and its edges (see src/graph.rs).
# CROSSCHECK_GRAPH_DIR=DIR keeps the graphs as DIR/<cfg name>.{tlc,rs}.dot (`tla2rs --graph-text`
# prints them in canonical form, for diffing), and the outputs as DIR/<cfg name>.{tlc,rs}.out
# (`tla2rs --messages-text` and `--trace-text` print their canonical forms).
graph() { "$bin" --graph "$1" || echo "graph unreadable"; }
# The state graph, or the file of the cfg's own -dump
graphs() {
  if [[ -n "$user_dump" ]]; then "$bin" --dump "$1.userdump" || echo "dump unreadable"; else graph "$1.dot"; fi
}
# The messages and printed lines, and the error lines among them, reduced to hashes (see
# src/messages.rs). For a large model, the lines of the checkpoints TLC writes every 30 minutes (with
# their paths and times) are left out first: only a long run has them
messages() {
  local f="$1"
  if [[ $large == 1 ]]; then
    grep -vE '^Checkpointing (of run |completed at \()' "$1" > "$1.nocp" || true
    f="$1.nocp"
  fi
  "$bin" --messages "$f" || echo "messages unreadable"
}
keep_graph() {
  [[ -n "${CROSSCHECK_GRAPH_DIR:-}" ]] || return 0
  mkdir -p "$CROSSCHECK_GRAPH_DIR"
  [[ -f "$1" ]] && cp "$1" "$CROSSCHECK_GRAPH_DIR/$(basename "$c" .cfg).$2.dot"
  [[ -f "$2.out" ]] && cp "$2.out" "$CROSSCHECK_GRAPH_DIR/$(basename "$c" .cfg).$2.out"
  return 0
}
expected_text() { echo "key $key"; echo "tlc $(grep -m1 -oE 'Version [0-9.]+' tlc.out || true)"; echo "rc $rc_tlc"; echo "$a"; }
fresh=0
[[ -n "$expected" && -f "$expected" && "$(sed -n 1p "$expected")" == "key $key" ]] && fresh=1

if [[ $mode != compare ]]; then
  [[ -n "$expected" ]] || { echo "ERROR $cfg_rel: not in examples/, tests/tlc/ or the corpus"; exit 1; }
  [[ $mode != expected-from || $large == 1 ]] || { echo "ERROR $cfg_rel: --expected-from is only for a model listed as large in tests/corpus.txt"; exit 1; }
  if [[ $mode == expected && $fresh == 1 ]]; then echo "fresh $cfg_rel"; exit 0; fi
fi
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for m in "${modules[@]}"; do cp "$spec_dir/$m.tla" "$work/"; done
cp "$cfg_abs" "$work/$c"
cd "$work"

if [[ $mode != compare ]]; then
  if [[ $mode == expected-from ]]; then
    cp "$from_out" tlc.out; rc_tlc=$from_rc; a=$(result tlc)
  else
    run_tlc
  fi
  if [[ -z "$(echo "$a" | head -1)" ]]; then
    echo "ERROR $cfg_rel: no verdict from TLC (exit $rc_tlc)"; sed 's/^/    tlc: /' tlc.out | grep -vE 'Parsing|Semantic' | head -10
    exit 1
  fi
  keep_graph tlc.dot tlc
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
rs_dump=(-dumpgraph rs.dot)
[[ -z "$user_dump" && $large == 0 ]] || rs_dump=()
"$bin" "$t" -config "$c" -o "$work/gen" -workers 1 ${rs_dump[@]+"${rs_dump[@]}"} -lassocheck "$work" ${extra[@]+"${extra[@]}"} ${rsonly[@]+"${rsonly[@]}"} > rs.out 2> rs.err || rc_rs=$?
[[ -z "$user_dump" ]] || mv "$user_dump" rs.userdump 2> /dev/null || true
[[ -z "$user_file" ]] || mv "$user_file" rs.userfile 2> /dev/null || true
s2=$(date +%s.%N)
# When a set or sequence outgrew the capacity the checker was built with, the checker made
# strings in another order than they were numbered in, or an EXCEPT warned while exploring,
# tla2rs built it again and checked from the start, after a line saying so: only the last run
# counts
restart='^tla2rs: .* checking again from the start with (room for [0-9]+|them in that order|the lines printed in TLC.s order)$'
grown=$(grep -cE "$restart" rs.out || true)
reordered=$(grep -cE '^tla2rs: .* with them in that order$' rs.out || true)
warned=$(grep -cE "^tla2rs: .* with the lines printed in TLC.s order$" rs.out || true)
grown=$((grown - reordered - warned))
if [[ $((grown + reordered + warned)) -gt 0 ]]; then
  last=$(grep -nE "$restart" rs.out | tail -1 | cut -d: -f1)
  tail -n +"$((last + 1))" rs.out > rs.last && mv rs.last rs.out
fi

# If the cfg says `\* crosscheck: distinct-only`, don't compare generated-state counts.
# TLC counts successors per \/ branch, so in specs where both branches can hold it counts the
# same successor more than once (distinct counts and verdicts still match).
distinct_only=0
if has_rule distinct-only; then
  distinct_only=1
fi

keep_graph rs.dot rs
b=$(result rs)
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
if has_rule ignore-exit; then
  a=$(echo "$a" | grep -v '^exit='); b=$(echo "$b" | grep -v '^exit=')
fi
# The state graph is compared as a whole (states and edges, see "State graphs" in CLAUDE.md), except:
# - TLC did not end its graph file: it stopped while computing the initial states or before, and
#   what it had buffered is lost. The graph is not compared
# - tla2rs stopped at a successor that left its declared type while being built: TLC adds that
#   state, but tla2rs cannot print it. Only the numbers of states and edges and the length of the
#   counterexample are compared
# - the model is listed as large: neither side wrote a graph
graph_note=""
if grep -q '^states incomplete' <<< "$a"; then
  a=$(grep -vE '^(states|edges) ' <<< "$a"); b=$(grep -vE '^(states|edges) ' <<< "$b")
  graph_note="; graph not compared: TLC stopped before ending it"
elif [[ -n "$user_dump" ]] && grep -q '^dump 0 ' <<< "$a"; then
  # The same for the cfg's own -dump: TLC's file is empty, as it stopped before writing what it
  # had buffered (in the initial states, or at start)
  a=$(grep -v '^dump ' <<< "$a"); b=$(grep -v '^dump ' <<< "$b")
  graph_note="; dump not compared: TLC stopped before writing it"
elif grep -q '<a successor that tla2rs cannot represent>' rs.out; then
  a=$(sed -E 's/^(states|edges|trace) ([0-9]+) [0-9a-f]+$/\1 \2/' <<< "$a"); b=$(sed -E 's/^(states|edges|trace) ([0-9]+) [0-9a-f]+$/\1 \2/' <<< "$b")
  graph_note="; graph and counterexample sizes only: a successor tla2rs cannot represent"
fi
[[ $large == 0 ]] || graph_note="$graph_note; large: no state graph"
# `\* crosscheck: error-lines (reason)` compares only the error lines among the messages, for a
# configuration where tla2rs cannot print all of TLC's text (the reason says why; see "Messages and
# printed lines" in CLAUDE.md)
if has_rule error-lines; then
  a=$(grep -v '^messages ' <<< "$a"); b=$(grep -v '^messages ' <<< "$b")
  graph_note="$graph_note; messages: error lines only"
fi
if [[ $distinct_only == 1 ]]; then
  a=$(echo "$a" | sed 's/^[0-9]* states generated //'); b=$(echo "$b" | sed 's/^[0-9]* states generated //')
fi
# A liveness counterexample is compared with TLC's like any other. Where the checker cannot follow
# TLC's search (it says why on stderr: TLC's tableau, a model value, VIEW or SYMMETRY) and prints a
# lasso of its own that differs from TLC's, TLC checks that lasso instead: the checker writes a spec
# whose only behavior is the lasso (-lassocheck, see src/lasso.rs), and TLC must report that it
# violates the properties, with one distinct state per state of the lasso. That holds only if the
# lasso starts in an initial state, each step is a step of the spec, it satisfies the spec's fairness
# and violates a property
lasso_note=""
if grep -q '^Temporal property violated' <<< "$a" && [[ "$(grep '^trace ' <<< "$a")" != "$(grep '^trace ' <<< "$b")" ]]; then
  lasso_why=$(grep -m1 -oE "the counterexample is tla2rs's own, not TLC's \(.*\)|TLC's search found no counterexample" rs.err | sed -E "s/.*not TLC's \((.*)\)$/\1/" || true)
  if [[ -n $lasso_why ]]; then
    a=$(sed 's/^trace .*/trace lasso/' <<< "$a"); b=$(sed 's/^trace .*/trace lasso/' <<< "$b")
    graph_note="$graph_note; lasso confirmed instead: $lasso_why"
  fi
fi
if [[ "$a" == "$b" ]] && grep -q '^trace lasso' <<< "$b"; then
  if [[ ! -f Tla2rsLasso.tla ]]; then
    echo "  LASSO NOT CHECKED: $(grep -m1 'lasso check is not written' rs.out || echo 'the checker wrote no lasso check')"
    exit 1
  fi
  # The states of the lasso (with -continue, the behaviors to violated invariants come before it)
  n_lasso=$(sed -n '/^Error: Temporal propert/,$p' rs.out | grep -cE '^State [0-9]+: <' || true)
  # TLC's answer depends only on the jar, the generated check and the spec's modules, so a
  # confirmation is kept in target/crosscheck/lasso under a hash of those, and TLC runs again only
  # when tla2rs writes a different lasso (CROSSCHECK_NO_CACHE=1 always runs it)
  lasso_key=$({ echo "lasso v1 $n_lasso"; shasum -a 256 "$jar" | cut -d' ' -f1; [[ $uses_cm == 0 ]] || echo "community $cm_sha256"
    for f in Tla2rsLasso.tla Tla2rsLasso.cfg "${modules[@]/%/.tla}"; do echo "== $f"; cat "$f"; done; } | shasum -a 256 | cut -d' ' -f1)
  lasso_ok="$root/target/crosscheck/lasso/$lasso_key"
  if [[ -n "${CROSSCHECK_NO_CACHE:-}" || ! -f "$lasso_ok" ]]; then
    rc_lasso=0
    set_tlc_cp
    mkdir -p "$work/jtmp"
    java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$tlc_cp" tlc2.TLC -workers 1 -config Tla2rsLasso.cfg Tla2rsLasso.tla > lasso.out 2>&1 || rc_lasso=$?
    found=$(grep -oE '[0-9,]+ distinct states found' lasso.out | tail -1 | tr -d ',' | cut -d' ' -f1 || true)
    if [[ $rc_lasso != 13 || "$found" != "$n_lasso" ]] || ! grep -q 'Temporal properties were violated' lasso.out; then
      echo "  LASSO NOT CONFIRMED by TLC (exit $rc_lasso, ${found:-no} distinct states for a lasso of $n_lasso)"
      grep -E '^Error|distinct states found|No error' lasso.out | head -5 | sed 's/^/    tlc: /'
      exit 1
    fi
    mkdir -p "$(dirname "$lasso_ok")" && touch "$lasso_ok"
    lasso_note="  (lasso of $n_lasso states confirmed by TLC)"
  else
    lasso_note="  (lasso of $n_lasso states confirmed by TLC earlier; cached)"
  fi
fi
note=""; [[ $tlc_cached == 1 ]] && note=" cached"
rebuilt=""; [[ $grown -gt 0 ]] && rebuilt="; rebuilt $grown more times with more room"
[[ $reordered -gt 0 ]] && rebuilt="$rebuilt; rebuilt $reordered more times for the order of strings made"
[[ $warned -gt 0 ]] && rebuilt="$rebuilt; rebuilt once for an EXCEPT warning"
printf '%-14s TLC %6.2fs%s | tla2rs %6.2fs (incl. build%s)\n' "$t" "$(echo "$s1 - $s0" | bc)" "$note" "$(echo "$s2 - $s1" | bc)" "$rebuilt"
if [[ "$a" == "$b" ]]; then
  if [[ $distinct_only == 1 ]]; then
    echo "  MATCH(distinct only; TLC counts \\/-duplicates$graph_note): $(echo "$a" | tr '\n' ' ')"
  elif [[ -n $graph_note ]]; then
    echo "  MATCH(${graph_note#; }): $(echo "$a" | tr '\n' ' ')"
  else
    echo "  MATCH: $(echo "$a" | tr '\n' ' ')"
  fi
  [[ -z $lasso_note ]] || echo "$lasso_note"
else
  echo "  MISMATCH"; echo "  TLC:    $(echo "$a" | tr '\n' ' ')"; echo "  tla2rs: $(echo "$b" | tr '\n' ' ')"
  sed 's/^/    rs.err: /' rs.err | head -20
  exit 1
fi
