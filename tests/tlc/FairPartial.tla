---- MODULE FairPartial ----
\* A fair action that leaves y unspecified: TLC stops with an error when it evaluates whether the
\* action is enabled, after the successors of the state (also for ENABLED in a property)
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A == x < 2 /\ x' = x + 1
Next == (A /\ y' = y) \/ (x = 2 /\ x' = 0 /\ y' = y)
Spec == Init /\ [][Next]_vars /\ WF_vars(A)
SpecNoFair == Init /\ [][Next]_vars
P == []<>(x = 2)
Q == []<>ENABLED A
====
