---- MODULE IntervalSetElem ----
\* An interval keeps its form inside the records, tuples and sequences a set held in the state
\* holds (as an array or a bitmask), also through \cup, \ and a filter, inside a function, from a
\* constant set, and when taken out again (CHOOSE, \E, \in); so does an empty function there, and
\* an interval in a set of sets over more than 10 integers. The invariant compares ToString with
\* the text TLC makes
EXTENDS Naturals, Sequences, TLC
VARIABLES r, t, q, e, b, k, f, m, x, y, w, n
Init == /\ r = {[a |-> 1..2, c |-> 0]}
        /\ t = {<<2..3, 0>>, <<{4}, 1>>}
        /\ q = {<<1..2>>}
        /\ e = {[i \in {} |-> 0]}
        /\ b = {1..12, {3, 4}}
        /\ k = {[a |-> 1..2]}
        /\ f = [i \in 1..2 |-> {[a |-> 1..i, c |-> i]}]
        /\ m = {[a |-> 1..i, c |-> i] : i \in 1..2}
        /\ x = {} /\ y = <<{}, 0>> /\ w = [a |-> {}, c |-> 0]
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ r' = IF n = 0 THEN r \cup {[a |-> {1, 2}, c |-> 0], [a |-> 2..3, c |-> 1]}
                ELSE {z \in r : z.c = 0}
        /\ t' = t \ {<<{4}, 1>>}
        /\ q' = q \cup {<<3..4, 5..6>>}
        /\ e' = e \cup {<<>>}
        /\ b' = b \cup {5..11}
        /\ k' = k \cup {[a |-> {1}], [a |-> 1..2]}
        /\ f' = [f EXCEPT ![1] = @ \cup {[a |-> 3..4, c |-> 0]}]
        /\ m' = {z \in m : z.c > n}
        /\ w' \in m
        /\ x' = (CHOOSE z \in r : z.c = 0).a
        /\ \E z \in t : y' = z
        /\ PrintT(<<n, r, t, q, e, b, k, f, m>>)
Inv == /\ ToString(x) \in {"{}", "1..2"}
       /\ ToString(y) \in {"<<{}, 0>>", "<<2..3, 0>>", "<<{4}, 1>>"}
       /\ ToString(w.a) \in {"{}", "1..1", "1..2"}
Short == n < 2
====
