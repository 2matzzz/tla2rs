---- MODULE PartFuns ----
\* Functions over sets from the state: [S -> T] and [x \in S |-> e] with S from the state,
\* Permutations of a set from the state, :> and @@, DOMAIN, application, and CHOOSE among them
EXTENDS Integers, TLC, FiniteSets
CONSTANTS Procs
VARIABLES S, f, g
Init == S = {} /\ f = << >> /\ g = [p \in Procs |-> 0]
Next == \/ \E p \in Procs \ S :
             /\ S' = S \cup {p}
             /\ f' = CHOOSE h \in [S' -> 0..1] : h # f /\ \A q \in DOMAIN h : h[q] = IF q = p THEN 1 ELSE 0
             /\ UNCHANGED g
        \/ /\ S # {}
           /\ g' = [q \in Procs |-> IF q \in DOMAIN f THEN f[q] ELSE 2]
           /\ f' = (CHOOSE q \in S : TRUE) :> 0 @@ f
           /\ UNCHANGED S
Inv == /\ DOMAIN f \subseteq S
       /\ \A q \in DOMAIN f : f[q] \in 0..1
       /\ f \in [DOMAIN f -> 0..1]
       /\ Cardinality(Permutations(S)) = IF Cardinality(S) = 3 THEN 6 ELSE IF Cardinality(S) = 2 THEN 2 ELSE 1
       /\ [q \in S |-> 0] = [q \in S |-> 0] @@ f
       /\ g @@ f = g
\* Violated: the counterexample prints functions over part of Procs
Few == Cardinality(DOMAIN f) < 2 \/ g = [p \in Procs |-> 0]
====
