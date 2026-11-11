---- MODULE ChooseRec ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
VARIABLES S, c
U == [k : 0..1, v : {"c", "a"}]
TypeOK == S \subseteq U /\ c \in U \cup {[k |-> 9, v |-> "z"]}
Init == S = {} /\ c = [k |-> 9, v |-> "z"]
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE [k |-> 9, v |-> "z"]
Inv == c # [k |-> 1, v |-> "c"] \/ Cardinality(S) < 2
====
