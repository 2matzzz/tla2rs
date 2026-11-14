---- MODULE IntervalSetElem ----
\* An interval keeps its form inside the records, tuples and sequences a set held in the state
\* holds, also through \cup, \ and a filter, and when taken out again (CHOOSE, \E); so does an empty
\* function there, and an interval in a set of sets over more than 10 integers. The invariant
\* compares ToString with the text TLC makes
EXTENDS Naturals, Sequences, TLC
VARIABLES r, t, q, e, b, x, y, n
Init == /\ r = {[a |-> 1..2, c |-> 0]}
        /\ t = {<<2..3, 0>>, <<{4}, 1>>}
        /\ q = {<<1..2>>}
        /\ e = {[i \in {} |-> 0]}
        /\ b = {1..12, {3, 4}}
        /\ x = {} /\ y = <<{}, 0>>
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ r' = IF n = 0 THEN r \cup {[a |-> {1, 2}, c |-> 0], [a |-> 2..3, c |-> 1]}
                ELSE {z \in r : z.c = 0}
        /\ t' = t \ {<<{4}, 1>>}
        /\ q' = q \cup {<<3..4, 5..6>>}
        /\ e' = e \cup {<<>>}
        /\ b' = b \cup {5..11}
        /\ x' = (CHOOSE z \in r : z.c = 0).a
        /\ \E z \in t : y' = z
        /\ PrintT(<<n, r, t, q, e, b>>)
Inv == /\ ToString(x) \in {"{}", "1..2"}
       /\ ToString(y) \in {"<<{}, 0>>", "<<2..3, 0>>", "<<{4}, 1>>"}
====
