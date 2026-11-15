#!/usr/bin/env bash
# Behavior check for the configurations of TlcGetLost.tla (see "Intentional differences" in CLAUDE.md):
# every behavior the checker printed must be one of the spec, whatever the registers held. It starts in
# an initial state (x >= 0), each step is A or NextD (x + 1) or B (x plus a positive multiple of 100),
# and its last state is one where the error printed before it occurs.
#   TlcGetLost.behaviors.sh OUT
set -uo pipefail
if grep -qE 'Failed to recover|could not reconstruct|probably a TLC bug' "$1"; then
  echo "the output says a behavior could not be rebuilt"; exit 1
fi
awk '
function fail(m) { print m; bad = 1; exit 1 }
function close_block() {
  if (!inb) return
  inb = 0
  if (n == 0) fail("a behavior with no states")
  if (want == "Deadlock") ok = (x >= 1000 || (nextd && x >= 3))
  else if (want == "Lost") ok = (x == 101)
  else if (want == "Pre") ok = (x == 303)
  else if (want == "Succ") ok = (x == 301)
  else if (want == "InitLost") ok = (x == 3)
  else if (want == "First" || want == "Eval") ok = (x == 100)
  else fail("a behavior after no known error (" want ")")
  if (!ok) fail("a behavior for " want " ends at x = " x)
  blocks++
}
/^Error: The behavior up to this point is:/ { close_block(); inb = 1; n = 0; nextd = 0; next }
/^Error: / || /states generated/ { close_block() }
/^Error: Invariant [A-Za-z0-9_]+ is violated/ { want = $3 }
/^Error: Evaluating invariant [A-Za-z0-9_]+ failed/ { want = $4; sub(/\.$/, "", want) }
/^Error: Deadlock reached/ { want = "Deadlock" }
inb && /^State [0-9]+: </ {
  k = $2; sub(/:$/, "", k); lab = $3; sub(/^</, "", lab)
  if (k != n + 1) fail("state " k " after state " n)
  getline v
  if (v !~ /^x = -?[0-9]+$/) fail("state " k " is not x = <integer>: " v)
  y = substr(v, 5) + 0
  if (k == 1) { if (lab != "Initial" || y < 0) fail("state 1 is not an initial state: " lab " x = " y) }
  else if (lab == "A" || lab == "NextD") { if (y != x + 1) fail(lab " from x = " x " to x = " y); if (lab == "NextD") nextd = 1 }
  else if (lab == "B") { d = y - x; if (d <= 0 || d % 100 != 0) fail("B from x = " x " to x = " y) }
  else fail("state " k " comes from an unknown action " lab)
  x = y; n = k
}
END { if (bad) exit 1; close_block(); if (bad) exit 1; print "ok " blocks " behaviors" }
' "$1"
