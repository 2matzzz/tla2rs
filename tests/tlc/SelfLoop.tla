---- MODULE SelfLoop ----
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
TypeOK == x \in 0..1 /\ y \in 0..1
Init == x = 0 /\ y = 0
A == x = 0 /\ x' = x /\ y' = y
B == x' = 1 - x /\ y' = y
C == y' = 1 - y /\ x' = x
Next == A \/ B \/ C
Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(C)
Prop == <>(x = 1)
Prop2 == []<>(y = 1)
====
