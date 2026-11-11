---- MODULE RejTupleCross ----
\* TLC stops with an error when it checks whether a non-tuple (here an integer) is in A \X B
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..2
Init == x = 0
Next == /\ x' = (x + 1) % 3
        /\ x = 0 \/ ~(x \in {1, 2} \X {3})
====
