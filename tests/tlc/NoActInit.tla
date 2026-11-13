---- MODULE NoActInit ----
\* A next-state relation without actions and no initial states: TLC reports the missing actions
\* only once it has an initial state to expand, so it finishes without an error
EXTENDS Naturals, TLC
VARIABLE x
Init == PrintT("init") /\ x = 0 /\ x > 1
Next == \E e \in {} : x' = e
====
