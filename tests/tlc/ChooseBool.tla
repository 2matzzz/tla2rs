---- MODULE ChooseBool ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
VARIABLES S, c
U == BOOLEAN
TypeOK == S \subseteq U /\ c \in U \cup {FALSE}
Init == S = {} /\ c = FALSE
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE FALSE
Inv == c # TRUE \/ Cardinality(S) < 2
====
