---- MODULE ChooseModel ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
CONSTANTS Procs, Dflt, Target
VARIABLES S, c
U == Procs
TypeOK == S \subseteq U /\ c \in U \cup {Dflt}
Init == S = {} /\ c = Dflt
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE Dflt
Inv == c # Target \/ Cardinality(S) < 2
====
