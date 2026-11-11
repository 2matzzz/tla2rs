---- MODULE ViewInv ----
\* (1, 1) has the same view as (1, 0), reached one level earlier, so it is not a new state and TLC
\* never checks the invariants on it
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == \/ x < 2 /\ x' = x + 1 /\ y' = y
        \/ x = 1 /\ y' = 1 /\ x' = x
View == x
Inv == y = 0
InvEval == y = 1 => 1 \div (y - y) = 0
====
