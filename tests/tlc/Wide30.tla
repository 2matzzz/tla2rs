---- MODULE Wide30 ----
\* A tuple of 30 elements and a record of 14 fields (stored as nested Rust tuples)
EXTENDS Naturals
VARIABLES t, r
Init == /\ t = [i \in 1..30 |-> 0] /\ t = <<0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0>>
        /\ r = [a |-> 0, b |-> 0, c |-> 0, d |-> 0, e |-> 0, f |-> 0, g |-> 0, h |-> 0, i |-> 0, j |-> 0, k |-> 0, l |-> 0, m |-> 0, n |-> FALSE]
Next == \/ \E k \in {1, 13, 25, 30} : t' = [t EXCEPT ![k] = (@ + 1) % 2] /\ UNCHANGED r
        \/ r' = [r EXCEPT !.n = ~@, !.m = (@ + 1) % 3] /\ UNCHANGED t
Inv == t[30] < 2 /\ r.m < 3 /\ DOMAIN t = 1..30
\* Violated
Both == ~(t[13] = 1 /\ t[30] = 1 /\ r.n)
====
