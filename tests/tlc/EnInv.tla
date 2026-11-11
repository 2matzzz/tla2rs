---- MODULE EnInv ----
\* ENABLED in invariants, and []P with ENABLED in P, which TLC checks as an invariant
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ UNCHANGED y
Reset == x = 2 /\ y = 1 /\ x' = 0 /\ UNCHANGED y
Flip == y' = 1 - y /\ UNCHANGED x
Next == Inc \/ Reset \/ Flip
Spec == Init /\ [][Next]_vars
Inv == ENABLED Inc \/ ENABLED Reset
Inv2 == \A k \in {0, 1} : (x = k) => ENABLED Inc
Prop == [](ENABLED Inc \/ ENABLED Reset)
====
