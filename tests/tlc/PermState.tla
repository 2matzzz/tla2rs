---- MODULE PermState ----
\* CHOOSE among the permutations of a set from the state, and \E over [S -> T] with S from the
\* state, in TLC's order
EXTENDS Integers, TLC, FiniteSets
VARIABLES S, p, h
TypeOK == S \subseteq 1..3
Init == S = {1} /\ p = [x \in {1} |-> 1] /\ h = [x \in {1} |-> 0]
Next == \/ /\ Cardinality(S) < 3
           /\ S' = S \cup {Cardinality(S) + 1}
           /\ p' = CHOOSE q \in Permutations(S') : q # [x \in S' |-> x] /\ q[1] # 1
           /\ \E k \in [S' -> {0, 1}] : k # [x \in S' |-> 0] /\ h' = k
        \/ /\ S # {1}
           /\ \E k \in [S -> {0, 1}] : k # h /\ h' = k
           /\ UNCHANGED <<S, p>>
Inv == DOMAIN p = S /\ DOMAIN h = S
\* Violated
NotThat == ~(Cardinality(S) = 3 /\ p[1] = 2 /\ h[2] = 1)
====
