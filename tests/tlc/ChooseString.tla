---- MODULE ChooseString ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
VARIABLES S, c
U == {"c", "a", "b"}
TypeOK == S \subseteq U /\ c \in U \cup {"none"}
Init == S = {} /\ c = "none"
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE "none"
Inv == c # "b" \/ Cardinality(S) < 2
====
