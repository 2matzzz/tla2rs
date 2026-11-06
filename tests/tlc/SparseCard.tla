---- MODULE SparseCard ----
\* Cardinality of a set too large for a bitmask (stored sparse).
EXTENDS Naturals, FiniteSets
VARIABLES s, x
TypeOK == /\ s \subseteq [a: 0..15, b: 0..15]
          /\ x \in 0..4
Init == s = {} /\ x = 0
Next == /\ x < 4
        /\ x' = x + 1
        /\ s' = IF Cardinality(s) < 2 THEN s \cup {[a |-> x, b |-> 15 - x]} ELSE s
Inv == Cardinality(s) <= 2
====
