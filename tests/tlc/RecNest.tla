---- MODULE RecNest ----
\* A set held as an array (its element type has more than 128 values) of records with a field that
\* is a record of different fields: ordered as TLC compares records, field by field
EXTENDS Naturals, FiniteSets
VARIABLE s
Kinds == {[a |-> 1], [a |-> 1, b |-> 2]}
Init == s = {}
Next == /\ Cardinality(s) < 2
        /\ \E i \in {0, 39, 40}, x \in Kinds : [k |-> i, r |-> x] \notin s /\ s' = s \cup {[k |-> i, r |-> x]}
TypeOK == s \subseteq [k : 0..100, r : Kinds]
Small == Cardinality(s) < 2 \/ \A e \in s : e.k = 0
====
