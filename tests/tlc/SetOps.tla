---- MODULE SetOps ----
EXTENDS Integers, FiniteSets
VARIABLE s, t, n
TypeOK == /\ s \in SUBSET (0..4)
          /\ t \subseteq -2..2
          /\ n \in -3..3
Init == /\ s \in SUBSET {0, 1}
        /\ t = {}
        /\ n \in {-1, 1}
Next == \/ /\ \E e \in (0..4) \ s :
                /\ s' = s \cup {e}
                /\ t' = {x \in t : x # n} \cup {(n % 3) - 1}
           /\ n' = n
        \/ /\ s # {}
           /\ \E e \in s : s' = s \ {e}
           /\ t' = {-x : x \in t}
           /\ n' \in {m \in -3..3 : m \notin t /\ m * m <= 4}
        \/ /\ t \subseteq s
           /\ s = {x + 0 : x \in s \cap 0..2}
           /\ UNCHANGED <<s, t>>
           /\ n' = -n
Inv == /\ Cardinality(s) + Cardinality(t) < 8
       /\ (t \cap s) \subseteq (s \cup t)
       /\ ~(s = {0, 1, 2, 3, 4} /\ t = {0})
====
