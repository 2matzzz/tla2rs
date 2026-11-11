---- MODULE TupleSets ----
\* Sets of tuples: a small element type (u128 bitmask) and one over 128 values (sorted array).
EXTENDS Naturals, FiniteSets
CONSTANTS Procs
VARIABLES small, big
TypeOK == /\ small \subseteq Procs \X (0..2)
          /\ big \subseteq (0..11) \X (0..11)
          /\ Cardinality(big) <= 3
Init == small = {} /\ big = {<<0, 0>>}
Next == \/ \E p \in Procs, k \in 0..2 :
             /\ <<p, k>> \notin small
             /\ small' = small \cup {<<p, k>>}
             /\ UNCHANGED big
        \/ \E t \in big :
             /\ t[1] < 7
             /\ Cardinality(big) < 3
             /\ big' = big \cup {<<t[1] + 5, (t[2] + 7) % 12>>}
             /\ UNCHANGED small
        \/ \E t \in big : t # <<0, 0>> /\ big' = big \ {t} /\ UNCHANGED small
Inv == /\ \A t \in big : t[1] % 5 = 0
       /\ Cardinality({t \in small : t[2] = 2}) <= 2
       /\ <<0, 0>> \in big
       /\ {t[1] : t \in small} \subseteq Procs
       /\ \A t \in small : t \in {u[1] : u \in small} \X {u[2] : u \in small}
       /\ <<0, 0, 0>> \notin big
====
