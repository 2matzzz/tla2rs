---- MODULE EmptyElem ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
\* The bound variable of a filter over {} is an element of no set: a test on it is never evaluated
Next == /\ {c \in {} : x \in c} = {}
        /\ \A c \in {} : x \in c
        /\ x' = 1 - x
====
