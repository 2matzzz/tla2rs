---- MODULE BigSubset ----
\* SUBSET of a set whose elements come from a large range (held as an array, not a bitmask)
EXTENDS Integers, FiniteSets
VARIABLES items, pick
TypeOK == items \subseteq 0..300 /\ Cardinality(items) <= 4 /\ pick \subseteq 0..300
Init == items = {} /\ pick = {}
Next == \/ \E x \in {299, 7, 150} \ items :
             /\ items' = items \cup {x}
             /\ pick' = CHOOSE t \in SUBSET items' : Cardinality(t) = 2 \/ t = items'
        \/ /\ Cardinality(items) = 3
           /\ \E t \in SUBSET items : Cardinality(t) = 1 /\ pick' = t /\ UNCHANGED items
        \/ /\ Cardinality(items) = 3
           /\ UNCHANGED <<items, pick>>
Inv == /\ Cardinality(SUBSET items) = 2 ^ Cardinality(items)
       /\ pick \in SUBSET items
       /\ \A t \in SUBSET items : t \subseteq items
       /\ {} \in SUBSET items
       /\ SUBSET items = {t \in SUBSET items : Cardinality(t) >= 0}
       /\ SUBSET pick \subseteq SUBSET items
\* Violated
NoPair == pick # {7, 299}
====
