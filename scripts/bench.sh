#!/usr/bin/env bash
# Run the same configuration with TLC and tla2rs and compare exploration times.
#   scripts/bench.sh Spec.tla Spec.cfg [-deadlock] [-setcap N]
# tla2rs build time is reported separately (paid once per spec change).
set -uo pipefail
tla="$1"; shift
cfg="${tla%.tla}.cfg"
if [[ $# -gt 0 && "$1" == *.cfg ]]; then cfg="$1"; shift; fi
extra=(); rsonly=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -setcap|-memlimit|-tmpdir) rsonly+=("$1" "$2"); shift 2 ;;
    -notrace|-fp128|-metal|-batched) rsonly+=("$1"); shift ;;
    *) extra+=("$1"); shift ;;
  esac
done
jar="${TLA_TOOLS:-$HOME/.tla/tla2tools.jar}"
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
cp "$tla" "$cfg" "$work/"; cd "$work"
t=$(basename "$tla"); c=$(basename "$cfg")

secs() { python3 -c 'import time;print(f"{time.time():.3f}")'; }
num() { grep -oE '[0-9,]+ distinct states found' "$1" | tail -1 | tr -d ',' | grep -oE '^[0-9]+'; }

s0=$(secs)
java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -workers auto -config "$c" ${extra[@]+"${extra[@]}"} "$t" > tlc.out 2>&1 || true
s1=$(secs)
"$root/target/release/tla2rs" "$t" -config "$c" -o "$work/gen" --emit-only ${rsonly[@]+"${rsonly[@]}"} > /dev/null 2>&1
(cd gen && cargo build --release --quiet 2>/dev/null)
s2=$(secs)
bin=$(ls gen/target/release/check_* 2>/dev/null | grep -v '\.d$' | head -1)
"$bin" ${extra[@]+"${extra[@]}"} ${rsonly[@]+"${rsonly[@]}"} > rs.out 2>&1 || true
s3=$(secs)

printf '%s / %s\n' "$t" "$c"
printf '  TLC     %7.1fs  %s distinct\n' "$(python3 -c "print($s1-$s0)")" "$(num tlc.out)"
printf '  tla2rs  %7.1fs  %s distinct  (+ %.1fs build)\n' "$(python3 -c "print($s3-$s2)")" "$(num rs.out)" "$(python3 -c "print($s2-$s1)")"
