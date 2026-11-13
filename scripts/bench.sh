#!/usr/bin/env bash
# Measure TLC and tla2rs on the same configurations, to find those where tla2rs is slower than TLC.
#   scripts/bench.sh [-auto] [-force] [-serial] [X.cfg ...]
#   scripts/bench.sh -corpus [-norun] [-auto] [-force] [-serial] [PATTERN ...]
# With no cfg, every configuration in examples/ and tests/tlc/. With -corpus, every model selected in
# tests/corpus.txt (`check` and `gap`; with -norun also the gaps marked norun), or only those whose cfg
# path contains one of the PATTERNs. For each configuration it measures the wall time and peak memory of
#   tlc         TLC with one worker, as scripts/expected.sh runs it (but without -dump)
#   tlc_auto    TLC with -workers auto (with -auto)
#   gen         tla2rs --emit-only: parsing the spec and writing the Rust code
#   build       cargo build of the generated crate from scratch (the build cache is not used)
#   check       the built checker alone, with one worker
#   check_auto  the built checker alone, with its default workers, one per CPU (with -auto)
# and the size of the generated code and of the checker. rs_total is gen + build + check: what
# `tla2rs Spec.tla -workers 1` costs from scratch. When a set or a sequence outgrows its capacity, or the
# checker makes strings in another order than they were numbered in, tla2rs builds the checker again
# (see "Capacities" and "The order of strings" in CLAUDE.md): the row then runs tla2rs itself, takes gen
# and build summed over the builds it did (column builds) and its wall time as rs_total, and check is
# the final checker run alone.
# Each row is kept in target/bench/rows/ and a later run skips it, so an interrupted run resumes where
# it stopped; -force measures again. At the end target/bench/results.tsv has every row kept (repository
# and corpus), and target/bench/summary.txt lists the configurations where tla2rs is slower than TLC,
# by ratio (`scripts/bench.sh -summary` prints it again).
# JOBS=N measures N configurations at a time (default 1, for accurate times). Runs with all workers
# always run alone; -serial also runs the other measured steps one at a time, so that only the work
# between them overlaps. BENCH_TIMEOUT=S stops a step after S seconds (default 1200), and its time is
# written as >S. Only target/bench/ is written (and target/community/, where crosscheck.sh also extracts
# the CommunityModules); tests/expected/ and target/crosscheck/ are not touched.
set -uo pipefail
cd "$(dirname "$0")/.."
root=$(pwd)
out="$root/target/bench"
jar="${TLA_TOOLS:-$HOME/.tla/tla2tools.jar}"
bin="$root/target/release/tla2rs"
unset TLA2RS_BUILD_CACHE
timeout="${BENCH_TIMEOUT:-1200}"
# The CommunityModules release TLC reads, as crosscheck.sh pins it
eval "$(grep -E '^cm_(version|sha256|names)=' scripts/crosscheck.sh)"

# measure.py LOCK LOCKFILE LIMIT OUT CMD...: runs CMD in a session of its own and writes "<wall s>
# <peak RSS KB> <exit code> <1 if stopped after LIMIT s>" to OUT. LOCK is s (shared) or x (exclusive) on
# LOCKFILE, or - for none; a gate lock keeps a waiting exclusive run from starving behind shared ones.
# The peak RSS is that of the largest process in the tree (cargo's includes rustc's)
measure_py='
import fcntl, os, signal, sys, threading, time
mode, lock, limit, out = sys.argv[1:5]
cmd = sys.argv[5:]
if mode != "-":
    gate, held = open(lock + ".gate", "a"), open(lock, "a")
    fcntl.flock(gate, fcntl.LOCK_EX)
    fcntl.flock(held, fcntl.LOCK_EX if mode == "x" else fcntl.LOCK_SH)
    gate.close()
t0 = time.monotonic()
pid = os.fork()
if pid == 0:
    os.setsid()
    try:
        os.execvp(cmd[0], cmd)
    except OSError as e:
        sys.stderr.write(f"{cmd[0]}: {e}\n")
        os._exit(127)
expired = []
def stop():
    try:
        os.killpg(pid, signal.SIGKILL)
    except OSError:
        pass
def expire():
    expired.append(1)
    stop()
for s in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(s, lambda n, f: (stop(), os._exit(128 + n)))
timer = threading.Timer(float(limit), expire)
timer.daemon = True
if float(limit) > 0:
    timer.start()
_, status, ru = os.wait4(pid, 0)
wall = time.monotonic() - t0
timer.cancel()
kb = ru.ru_maxrss // 1024 if sys.platform == "darwin" else ru.ru_maxrss
rc = os.WEXITSTATUS(status) if os.WIFEXITED(status) else 128 + os.WTERMSIG(status)
with open(out, "w") as f:
    f.write(f"{wall:.3f} {kb} {rc} {1 if expired else 0}\n")
'
# measure NAME LOCK CMD...: runs CMD in the work directory, its output in NAME.out and NAME.err, and
# sets m_s (">S" when stopped), m_mb and m_rc
measure() {
  local name=$1 lock=$2 kb to; shift 2
  [[ -n $BENCH_SERIAL ]] && lock=x
  [[ $BENCH_JOBS == 1 ]] && lock=-
  python3 -c "$measure_py" "$lock" "$out/lock" "$timeout" "$work/$name.m" "$@" > "$work/$name.out" 2> "$work/$name.err"
  read -r m_s kb m_rc to < "$work/$name.m" || { m_s=-; kb=0; m_rc=-; to=0; }
  m_mb=$(awk -v k="$kb" 'BEGIN { printf "%.1f", k / 1024 }')
  [[ $to == 1 ]] && m_s=">$timeout"
  return 0
}
distinct() { local d; d=$(grep -oE '[0-9,]+ distinct states found' "$1" 2> /dev/null | tail -1 | tr -d ',' | cut -d' ' -f1); echo "${d:--}"; }
# The sum of times, as a lower bound (">") if one of them is
add() { awk 'BEGIN { s = 0; lb = ""; for (i = 1; i < ARGC; i++) { x = ARGV[i]; if (sub(/^>/, "", x)) lb = ">"; s += x }; printf "%s%.3f", lb, s }' "$@"; }

# row SET ID TLA CFG RSARGS NAME: measures one configuration into target/bench/rows/SET/ID.tsv. RSARGS
# are tla2rs's extra arguments with commas for spaces ("-" for none), as in tests/corpus.txt
row() {
  local set=$1 id=$2 tla=$3 cfg=$4 rsargs=$5 name=$6
  local file="$out/rows/$set/$id.tsv"
  # A kept row counts as done, unless -auto asks for the runs with all workers and it has none
  if [[ -z $BENCH_FORCE && -f $file ]] && [[ -z $BENCH_AUTO || "$(cut -f5 "$file")" != - ]]; then return 0; fi
  [[ $rsargs == - ]] && rsargs=""
  local rsa=() chk=() i=0
  read -r -a rsa <<< "${rsargs//,/ }"
  # The arguments the checker takes too (the others only change the generated code)
  while [[ $i -lt ${#rsa[@]} ]]; do
    case "${rsa[$i]}" in
      -setcap|-seqcap) i=$((i + 2)) ;;
      -fp128) i=$((i + 1)) ;;
      *) chk+=("${rsa[$i]}"); i=$((i + 1)) ;;
    esac
  done
  # The modules of the spec's directory that the spec reads, and whether TLC needs the
  # CommunityModules, found as crosscheck.sh finds them
  local spec_dir t c m f n local_names modules=() queue uses_cm=0
  spec_dir=$(cd "$(dirname "$tla")" && pwd); t=$(basename "$tla"); c=$(basename "$cfg")
  local_names=$(cd "$spec_dir" && ls *.tla | sed 's/\.tla$//')
  queue=("${t%.tla}")
  while [[ ${#queue[@]} -gt 0 ]]; do
    m="${queue[0]}"; queue=("${queue[@]:1}")
    [[ -f "$spec_dir/$m.tla" && " ${modules[*]-} " != *" $m "* ]] || continue
    modules+=("$m")
    for f in $(grep -owF "$local_names" "$spec_dir/$m.tla" | sort -u); do queue+=("$f"); done
  done
  for m in ${modules[@]+"${modules[@]}"}; do
    for n in $(tr '\n' ' ' < "$spec_dir/$m.tla" | grep -oE '(EXTENDS|INSTANCE)[[:space:]]+[A-Za-z0-9_]+([[:space:]]*,[[:space:]]*[A-Za-z0-9_]+)*' | sed -E 's/^(EXTENDS|INSTANCE)//' | tr ',' ' '); do
      if [[ " $cm_names " == *" $n "* && ! -f "$spec_dir/$n.tla" ]]; then uses_cm=1; fi
    done
  done
  local tlc_cp="$jar"
  if [[ $uses_cm == 1 ]]; then
    local cmjar="${COMMUNITY_MODULES:-$HOME/.tla/CommunityModules-deps.jar}" cmdir="$root/target/community/$cm_sha256"
    if [[ ! -f "$cmdir/.extracted" ]]; then
      [[ "$(shasum -a 256 "$cmjar" 2> /dev/null | cut -d' ' -f1)" == "$cm_sha256" ]] || { echo "ERROR $name: needs $cmjar, CommunityModules-deps-$cm_version.jar (see CLAUDE.md)" >&2; return 1; }
      local tmp="$cmdir.tmp$$"
      rm -rf "$tmp" && mkdir -p "$tmp" && unzip -q -o "$cmjar" '*.tla' -d "$tmp" && touch "$tmp/.extracted" || return 1
      if [[ -d "$cmdir" ]]; then rm -rf "$tmp"; else mv "$tmp" "$cmdir" 2> /dev/null; fi
      rm -rf "$tmp" "$cmdir/$(basename "$tmp")"
    fi
    tlc_cp="$jar:$cmdir"
  fi
  work=$(mktemp -d "$out/work/$id.XXXXXX")
  trap 'rm -rf "$work"' EXIT
  for m in "${modules[@]}"; do cp "$spec_dir/$m.tla" "$work/"; done
  cp "$cfg" "$work/$c"
  cd "$work" || return 1
  mkdir -p jtmp

  local tlc_s tlc_mb tlc_rc tlc_auto_s=- tlc_auto_mb=- gen_s gen_mb build_s=- build_mb=- check_s=- check_mb=-
  local check_auto_s=- check_auto_mb=- rs_total code_kb=- bin_kb=- builds=0 rs_rc rs_out=check.out note="" checker=""
  # TLC: a private java.io.tmpdir, as TLC runs sharing one fail at random in SANY when run in parallel
  measure tlc s java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$tlc_cp" tlc2.TLC -workers 1 -config "$c" "$t"
  tlc_s=$m_s; tlc_mb=$m_mb; tlc_rc=$m_rc
  if [[ -n $BENCH_AUTO ]]; then
    measure tlc_auto x java -Djava.io.tmpdir="$work/jtmp" -XX:+UseParallelGC -cp "$tlc_cp" tlc2.TLC -workers auto -config "$c" "$t"
    tlc_auto_s=$m_s; tlc_auto_mb=$m_mb
  fi
  measure gen s "$bin" "$t" -config "$c" -o gen --emit-only ${rsa[@]+"${rsa[@]}"}
  gen_s=$m_s; gen_mb=$m_mb; rs_rc=$m_rc; rs_total=$m_s; rs_out=gen.out
  if [[ $m_rc != 0 || ! -f gen/src/main.rs ]]; then
    # A false ASSUME or a property TLC cannot check stops tla2rs here, as it stops TLC
    [[ $m_s == ">"* ]] || note="no checker: tla2rs exited with $m_rc"
  else
    code_kb=$(( $(wc -c < gen/src/main.rs) / 1024 ))
    measure build s cargo build --release --quiet --offline --manifest-path gen/Cargo.toml
    build_s=$m_s; build_mb=$m_mb; builds=1
    checker=$(ls gen/target/release/check_* 2> /dev/null | grep -v '\.d$' | head -1)
    if [[ $m_rc != 0 || -z $checker ]]; then
      [[ $m_s == ">"* ]] || note="build failed (exit $m_rc)"
      rs_rc=$m_rc; rs_total=$(add "$gen_s" "$build_s")
    else
      # As tla2rs runs it: exit 70/71 when a capacity must grow, 72 when strings must be renumbered
      measure check s env TLA2RS_GROW=sq TLA2RS_ORDER="$work/order.txt" "$checker" -workers 1 ${chk[@]+"${chk[@]}"}
      check_s=$m_s; check_mb=$m_mb; rs_rc=$m_rc; rs_out=check.out
      rs_total=$(add "$gen_s" "$build_s" "$check_s")
      if [[ $m_rc == 70 || $m_rc == 71 || $m_rc == 72 ]]; then
        rm -rf gen
        measure full s "$bin" "$t" -config "$c" -o gen -workers 1 ${rsa[@]+"${rsa[@]}"}
        rs_total=$m_s; rs_rc=$m_rc
        gen_s=$(grep -oE 'in [0-9]+ ms$' full.err | awk '{ s += $2 } END { printf "%.3f", s / 1000 }')
        build_s=$(grep -oE 'built in [0-9.]+ s$' full.err | awk '{ s += $3 } END { printf "%.3f", s }')
        builds=$(grep -cE 'built in [0-9.]+ s$' full.err)
        note="built $builds times (capacity or order of strings)"
        checker=$(ls gen/target/release/check_* 2> /dev/null | grep -v '\.d$' | head -1)
        check_s=-; check_mb=-; rs_out=full.out
        if [[ -n $checker && $m_rc != 70 && $m_rc != 71 && $m_rc != 72 && $m_s != ">"* ]]; then
          measure check s "$checker" -workers 1 ${chk[@]+"${chk[@]}"}
          check_s=$m_s; check_mb=$m_mb; rs_out=check.out
          [[ -f gen/src/main.rs ]] && code_kb=$(( $(wc -c < gen/src/main.rs) / 1024 ))
        fi
      fi
      [[ -n $checker && -f $checker ]] && bin_kb=$(( $(wc -c < "$checker") / 1024 ))
      if [[ -n $BENCH_AUTO && -n $checker && $check_s != - && $check_s != ">"* ]]; then
        measure check_auto x "$checker" ${chk[@]+"${chk[@]}"}
        check_auto_s=$m_s; check_auto_mb=$m_mb
      fi
    fi
  fi
  local d_tlc d_rs same=-
  d_tlc=$(distinct tlc.out); d_rs=$(distinct "$rs_out")
  if [[ $d_tlc != - || $d_rs != - ]]; then
    if [[ $d_tlc == "$d_rs" && $tlc_rc == "$rs_rc" ]]; then same=yes; else same=no; note="${note:+$note; }differs from TLC (distinct states or exit code)"; fi
  fi
  for x in tlc gen build check full; do
    [[ -f $x.m && "$(cut -d' ' -f4 $x.m)" == 1 ]] && note="${note:+$note; }$x stopped after $timeout s"
  done
  local jobs="$BENCH_JOBS"; [[ -n $BENCH_SERIAL ]] && jobs="$jobs-serial"
  mkdir -p "$(dirname "$file")"
  printf '%s\t' "$set" "$name" "$tlc_s" "$tlc_mb" "$tlc_auto_s" "$tlc_auto_mb" "$gen_s" "$gen_mb" "$build_s" "$build_mb" \
    "$check_s" "$check_mb" "$check_auto_s" "$check_auto_mb" "$rs_total" "$code_kb" "$bin_kb" "$builds" "$tlc_rc" "$rs_rc" \
    "$d_tlc" "$d_rs" "$same" "$jobs" "$BENCH_REV" > "$file.tmp$$"
  printf '%s\n' "${note:--}" >> "$file.tmp$$"
  mv "$file.tmp$$" "$file"
  printf '%-60s TLC %9s s | tla2rs check %9s s, total %9s s%s\n' "$name" "$tlc_s" "$check_s" "$rs_total" "${note:+  ($note)}"
}

header="set	config	tlc_s	tlc_mb	tlc_auto_s	tlc_auto_mb	gen_s	gen_mb	build_s	build_mb	check_s	check_mb	check_auto_s	check_auto_mb	rs_total_s	code_kb	bin_kb	builds	tlc_rc	rs_rc	tlc_distinct	rs_distinct	same	jobs	rev	note"

# slower RS TLC TITLE: the rows of results.tsv where column RS (tla2rs) is slower than column TLC, by ratio
slower() {
  local rs=$1 tl=$2 title=$3 all list n k
  all=$(awk -F'\t' -v rs="$rs" -v tl="$tl" 'NR > 1 && $rs != "-" && $tl != "-" {
      a = $rs; b = $tl; la = sub(/^>/, "", a); lb = sub(/^>/, "", b)
      n++
      if (lb || b <= 0) next
      if (a / b > 1) printf "%.6f\t%s%.1fx\t%s\t%s\t%s\n", a / b, (la ? ">" : ""), a / b, $tl, $rs, $2
    } END { printf "compared\t%d\n", n }' "$out/results.tsv")
  n=$(grep '^compared' <<< "$all" | cut -f2)
  [[ $n -gt 0 ]] || return 0
  list=$(grep -v '^compared' <<< "$all" | sort -t$'\t' -k1,1gr | cut -f2-)
  k=$(grep -c . <<< "$list")
  echo "$title: $k of $n"
  [[ $k -gt 0 ]] && { printf '  ratio\tTLC s\ttla2rs s\tconfiguration\n'; sed 's/^/  /' <<< "$list"; }
  echo
}
summary() {
  local n
  n=$(($(wc -l < "$out/results.tsv") - 1))
  echo "$n configurations: $(awk -F'\t' 'NR > 1 { n[$1]++ } END { for (k in n) printf "%s%s %d", (s++ ? ", " : ""), k, n[k] }' "$out/results.tsv")"
  awk -F'\t' 'NR > 1 && $3 !~ /^[->]/ && $11 !~ /^[->]/ && $15 !~ /^[->]/ && $3 > 0 && $11 > 0 && $15 > 0 {
      n++; c += log($3 / $11); t += log($3 / $15) }
    END { if (n) printf "geometric mean of TLC / tla2rs over %d configurations: check %.2fx, total %.2fx\n\n", n, exp(c / n), exp(t / n) }' "$out/results.tsv"
  slower 11 3 "tla2rs check (one worker) slower than TLC (one worker)"
  slower 15 3 "tla2rs total (generation + build + check) slower than TLC (one worker)"
  slower 13 5 "tla2rs check (default workers) slower than TLC (-workers auto)"
  local notes; notes=$(awk -F'\t' 'NR > 1 && $26 != "-" { printf "  %s\t%s\n", $2, $26 }' "$out/results.tsv")
  [[ -z $notes ]] || { echo "configurations with a note: $(grep -c . <<< "$notes")"; echo "$notes"; }
}

if [[ "${1:-}" == --row ]]; then
  shift
  row "$@"
  exit
fi

corpus=""; norun=""; args=()
export BENCH_AUTO="" BENCH_FORCE="" BENCH_SERIAL="" BENCH_JOBS="${JOBS:-1}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    -corpus) corpus=1 ;;
    -norun) norun=1 ;;
    -auto) BENCH_AUTO=1 ;;
    -force) BENCH_FORCE=1 ;;
    -serial) BENCH_SERIAL=1 ;;
    -summary) [[ -f $out/results.tsv ]] && summary; exit ;;
    -*) echo "usage: scripts/bench.sh [-corpus [-norun]] [-auto] [-force] [-serial] [X.cfg | PATTERN ...]" >&2; exit 2 ;;
    *) args+=("$1") ;;
  esac
  shift
done
export BENCH_REV; BENCH_REV=$(git describe --always --dirty 2> /dev/null || echo -)
cargo build --release --quiet || exit 1
# The configurations as "SET ID TLA CFG RSARGS NAME"
list() {
  if [[ -n $corpus ]]; then
    local dir; dir=$(scripts/corpus.sh -fetch) || return 1
    awk -v norun="$norun" '$1 == "check" || $1 == "gap" {
        rs = "-"; skip = 0
        for (i = 4; i <= NF && $i != "#"; i++) { if ($i ~ /^rsargs=/) rs = substr($i, 8); if ($i == "norun" && !norun) skip = 1 }
        if (!skip) print $2, $3, rs }' tests/corpus.txt |
      while read -r tla cfg rs; do
        if [[ ${#args[@]} -gt 0 ]]; then
          local hit=0 p
          for p in "${args[@]}"; do [[ $cfg == *"$p"* ]] && hit=1; done
          [[ $hit == 1 ]] || continue
        fi
        local id="${cfg#specifications/}"; id="${id%.cfg}"
        echo "corpus ${id//\//_} $dir/$tla $dir/$cfg $rs $cfg"
      done
  else
    local cfg rel base tla rs a
    if [[ ${#args[@]} -eq 0 ]]; then args=(examples/*.cfg tests/tlc/*.cfg); fi
    for cfg in "${args[@]}"; do
      [[ -f $cfg ]] || { echo "ERROR no such cfg: $cfg" >&2; continue; }
      rel="$(cd "$(dirname "$cfg")" && pwd)/$(basename "$cfg")"; rel="${rel#"$root"/}"
      base=$(basename "$cfg" .cfg); tla="$(dirname "$rel")/${base%%-*}.tla"
      [[ -f "$tla" ]] || tla="$(dirname "$rel")/$base.tla"
      rs=-
      if a=$(grep -m1 -oE '^[[:space:]]*\\\*[[:space:]]*crosscheck:[[:space:]]*rsargs[[:space:]].*' "$rel"); then
        read -r -a a <<< "${a#*rsargs}"; rs=$(IFS=,; echo "${a[*]}")
      fi
      local id="${rel%.cfg}"
      echo "repo ${id//\//_} $root/$tla $root/$rel $rs $rel"
    done
  fi
}
rm -rf "$out/work"; mkdir -p "$out/work" "$out/rows"
list | xargs -P "$BENCH_JOBS" -L1 scripts/bench.sh --row
rm -rf "$out/work"
{ echo "$header"; cat "$out"/rows/*/*.tsv 2> /dev/null | sort -t$'\t' -k1,1 -k2,2; } > "$out/results.tsv"
summary | tee "$out/summary.txt"
