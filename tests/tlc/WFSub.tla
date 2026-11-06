---- MODULE WFSub ----
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
TypeOK == x \in 0..1 /\ y \in 0..1
Init == x = 0 /\ y = 0
A == y' = 1 - y /\ UNCHANGED x
Next == A
Spec == Init /\ [][Next]_vars /\ WF_x(A)
Prop == []<>(y = 1)
====
