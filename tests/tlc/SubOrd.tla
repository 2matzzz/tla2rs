---- MODULE SubOrd ----
\* CHOOSE over SUBSET of a set in the state follows TLC's order of subsets: smaller ones first,
\* so {4} comes before {1, 2}
EXTENDS Integers, FiniteSets
VARIABLES S, c
P(T) == Cardinality(T) >= 2 \/ T = {4}
TypeOK == S \subseteq 1..4 /\ c \subseteq 1..4
Init == S = {} /\ c = {}
Next == \E e \in 1..4 :
          /\ S' = IF e \in S THEN S \ {e} ELSE S \cup {e}
          /\ c' = IF \E T \in SUBSET S' : P(T) THEN CHOOSE T \in SUBSET S' : P(T) ELSE {}
Inv == c # {4} \/ Cardinality(S) < 3
====
