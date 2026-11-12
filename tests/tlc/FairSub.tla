---- MODULE FairSub ----
\* A fair action that leaves y unspecified, with a subscript that reads only x: TLC computes whether
\* it is enabled without y, and the fairness holds (the property needs it)
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Step == x' = (x + 1) % 3
Flip == y' = 1 - y
Next == Step /\ (Flip \/ UNCHANGED y)
Spec == Init /\ [][Next]_vars /\ WF_x(Step)
P == []<>(x = 2)
Q == []<>(y = 1)
====
