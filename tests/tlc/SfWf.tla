---- MODULE SfWf ----
\* Go is enabled only every other state: weak fairness does not force it, strong fairness does
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Go == y = 0 /\ x = 0 /\ x' = 1 /\ UNCHANGED y
Flip == y' = 1 - y /\ UNCHANGED x
Next == Go \/ Flip
SpecW == Init /\ [][Next]_vars /\ WF_vars(Go) /\ WF_vars(Flip)
SpecS == Init /\ [][Next]_vars /\ SF_vars(Go) /\ WF_vars(Flip)
Done == <>(x = 1)
View == y
Con == y < 1 \/ x = 0
====
