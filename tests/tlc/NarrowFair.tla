---- MODULE NarrowFair ----
\* Next takes A only when y = 1, but fairness is about A itself: ENABLED <<A>>_v is decided on A
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
A == x' = 1 - x /\ UNCHANGED y
B == y' = 1 - y /\ UNCHANGED x
Next == (A /\ y = 1) \/ B
Spec == Init /\ [][Next]_vars /\ WF_vars(A)
SpecS == Init /\ [][Next]_vars /\ SF_vars(Next /\ x = 0) /\ WF_vars(B)
P == []<>(x = 1)
====
