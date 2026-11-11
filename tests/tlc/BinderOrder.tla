---- MODULE BinderOrder ----
\* TLC varies the first of several bound variables fastest, which decides how many states it
\* generates before it finds a violation
EXTENDS Naturals
VARIABLES a, b, c
Init == a = 0 /\ b = 0 /\ c = 0
Next == \/ \E p, q \in 1..3 : a' = p /\ b' = q /\ c' = 0
        \/ \E p \in 1..3, q \in {4, 5}, r \in 1..2 : a' = p /\ b' = q /\ c' = r
Inv == ~(a = 1 /\ b = 3)
Inv3 == ~(a = 2 /\ b = 4 /\ c = 2)
====
