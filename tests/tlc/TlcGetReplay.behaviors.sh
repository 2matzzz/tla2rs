#!/usr/bin/env bash
# Behavior check for the configurations of TlcGetReplay.tla (see "Intentional differences" in
# CLAUDE.md): every behavior the checker printed must be one of the spec, whatever the registers
# held. It starts in an initial state (x in 0..1), each step from an x below 50 is A (x + 2) or B
# (x plus 10 times a register value in 0..4), and its last state is one where the invariant reported
# before it fails to evaluate.
#   TlcGetReplay.behaviors.sh OUT
set -uo pipefail
awk '
function fail(m) { print m; bad = 1; exit 1 }
function close_block() {
  if (!inb) return
  inb = 0
  if (n == 0) fail("a behavior with no states")
  if (want == "Bad") ok = (x == 3)
  else if (want == "BadTwice") ok = (x == 3 || x == 41)
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
  if (k == 1) { if (lab != "Initial" || y < 0 || y > 1) fail("state 1 is not an initial state: " lab " x = " y) }
  else if (x >= 50) fail(lab " from x = " x)
  else if (lab == "A") { if (d != 2) fail("A from x = " x " to x = " y) }
  else if (lab == "B") { if (d < 0 || d > 40 || d % 10 != 0) fail("B from x = " x " to x = " y) }
  else fail("state " k " comes from an unknown action " lab)
  x = y; n = k
}
END { if (bad) exit 1; close_block(); if (bad) exit 1; print "ok " blocks " behaviors" }
' "$1"
