---- MODULE WFGuard ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..1
Init == x = 0
A == x' = 1 - x
Next == x # 0 /\ A
Spec == Init /\ [][Next]_x /\ WF_x(A)
Prop == <>(x = 1)
====
