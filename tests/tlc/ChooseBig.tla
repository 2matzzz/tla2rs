---- MODULE ChooseBig ----
\* CHOOSE over a set held in the state whose element type has more than 128 values (a sorted
\* array rather than a bitmask)
EXTENDS Integers, FiniteSets
VARIABLES S, c
TypeOK == S \subseteq (0..12) \X (0..12) /\ Cardinality(S) <= 3 /\ c \in (-1..12) \X (-1..12)
Init == S = {} /\ c = <<-1, -1>>
Next == \E e \in {<<3, 1>>, <<1, 7>>, <<1, 2>>, <<12, 0>>} :
          /\ S' = IF e \in S THEN S \ {e} ELSE IF Cardinality(S) < 3 THEN S \cup {e} ELSE S
          /\ c' = IF \E x \in S' : x # c THEN CHOOSE x \in S' : x # c ELSE <<-1, -1>>
Inv == c # <<1, 7>> \/ Cardinality(S) < 3
====
