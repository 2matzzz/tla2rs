---- MODULE IntervalExists ----
\* A name bound by \E over a constant set holds an element in the form TLC holds it, also through an
\* IF, in Init and in an action. The invariant compares ToString with the text TLC makes
EXTENDS Naturals, TLC
VARIABLES u, v, n
Init == /\ \E s \in {4..5, {6}} : v = s
        /\ u = {}
        /\ n = 0
Next == \/ /\ n < 2 /\ n' = n + 1
           /\ \E s \in {1..2, {3}}, k \in {0, 1} : u' = IF k = 0 THEN s ELSE {k}
           /\ v' = v
           /\ PrintT(<<u, v, ToString(u)>>)
        \/ n = 2 /\ UNCHANGED <<u, v, n>>
Inv == ToString(u) \in {"{}", "1..2", "{3}", "{1}"} /\ ToString(v) \in {"4..5", "{6}"}
====
