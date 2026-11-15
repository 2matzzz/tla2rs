#!/usr/bin/env bash
# Behavior check for the configurations of PrintAgain.tla and AgainTwice.tla, which have the same
# steps (see "Intentional differences" in CLAUDE.md): every behavior the checker printed must be one
# of the spec. It starts in an initial state (x in 0..2), each step adds 1, 2, 10 or 20 to an x below
# 9 (A, B, C, D, or Next for all four), and its last state is one where the invariant reported
# before it fails to evaluate.
#   PrintAgain.behaviors.sh OUT
set -uo pipefail
awk '
function fail(m) { print m; bad = 1; exit 1 }
function close_block() {
  if (!inb) return
  inb = 0
  if (n == 0) fail("a behavior with no states")
  if (want == "Bad") ok = (x == 4)
  else if (want == "BadTwice") ok = (x == 4 || x == 22)
  else fail("a behavior after no known error (" want ")")
  if (!ok) fail("a behavior for " want " ends at x = " x)
  blocks++
}
/^Error: The behavior up to this point is:/ { close_block(); inb = 1; n = 0; next }
/^Error: / || /states generated/ { close_block() }
/^Error: Evaluating invariant [A-Za-z0-9_]+ failed/ { want = $4 }
inb && /^State [0-9]+: </ {
  k = $2; sub(/:$/, "", k); lab = $3; sub(/^</, "", lab)
  if (k != n + 1) fail("state " k " after state " n)
  getline v
  if (v !~ /^x = -?[0-9]+$/) fail("state " k " is not x = <integer>: " v)
  y = substr(v, 5) + 0
  d = y - x
  if (k == 1) { if (lab != "Initial" || y < 0 || y > 2) fail("state 1 is not an initial state: " lab " x = " y) }
  else if (x >= 9) fail(lab " from x = " x)
  else if (lab == "A") { if (d != 1) fail("A from x = " x " to x = " y) }
  else if (lab == "B") { if (d != 2) fail("B from x = " x " to x = " y) }
  else if (lab == "C") { if (d != 10) fail("C from x = " x " to x = " y) }
  else if (lab == "D") { if (d != 20) fail("D from x = " x " to x = " y) }
  else if (lab == "Next") { if (d != 1 && d != 2 && d != 10 && d != 20) fail("Next from x = " x " to x = " y) }
  else fail("state " k " comes from an unknown action " lab)
  x = y; n = k
}
END { if (bad) exit 1; close_block(); if (bad) exit 1; print "ok " blocks " behaviors" }
' "$1"
