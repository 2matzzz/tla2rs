---- MODULE ExceptSplit ----
\* TLC splits the next-state relation into actions through \E over a constant set, evaluating
\* the set once, when it reads the spec: an EXCEPT there warns then, between the constant
\* definitions and the ASSUMEs
EXTENDS Naturals, TLC
VARIABLE x
C == PrintT("constant")
ASSUME PrintT("assume")
Init == x = 0
Next == \E i \in DOMAIN [<<1>> EXCEPT ![9] = 0] : x' = (x + i) % 3
\* Not split: \E inside a conjunction is evaluated each time
NextIn == x < 5 /\ \E i \in DOMAIN [<<1>> EXCEPT ![9] = 0] : x' = (x + i) % 3
\* An empty set: no successor, after the warning
NextEmpty == x < 5 /\ \E i \in DOMAIN [<<>> EXCEPT ![9] = 0] : x' = i
====
