---- MODULE AssertFail ----
\* A false Assert stops TLC with its own exit code
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ Assert(x < 2, "x is too large")
====
