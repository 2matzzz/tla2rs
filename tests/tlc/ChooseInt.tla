---- MODULE ChooseInt ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
VARIABLES S, c
U == 0..4
TypeOK == S \subseteq U /\ c \in U \cup {-1}
Init == S = {} /\ c = -1
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE -1
Inv == c # 3 \/ Cardinality(S) < 2
====
