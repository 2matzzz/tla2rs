---- MODULE ChooseTup ----
\* CHOOSE over a set held in the state picks the element TLC picks
EXTENDS Integers, FiniteSets
VARIABLES S, c
U == (0..1) \X {"c", "a"}
TypeOK == S \subseteq U /\ c \in U \cup {<<9, "z">>}
Init == S = {} /\ c = <<9, "z">>
Next == \E e \in U :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE <<9, "z">>
Inv == c # <<1, "c">> \/ Cardinality(S) < 2
====
