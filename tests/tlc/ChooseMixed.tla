---- MODULE ChooseMixed ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
CONSTANTS Dflt, Other
VARIABLES S, c
U == (1..2) \cup {Dflt, Other}
TypeOK == S \subseteq U /\ c \in U \cup {0}
Init == S = {} /\ c = 0
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE 0
Inv == c # 2 \/ Cardinality(S) < 2
====
