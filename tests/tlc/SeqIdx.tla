---- MODULE SeqIdx ----
\* A tuple index from the state out of range is an evaluation error
EXTENDS Naturals, Sequences
VARIABLES q, k
TypeOK == q \in Seq(1..2) /\ k \in 0..4
Init == q = <<1, 2>> /\ k = 1
Next == /\ q' = Tail(q)
        /\ k' = k + 1
        /\ Head(q) > 0
        /\ <<5, 6, 7>>[k + 2] > 0
Bound == Len(q) <= 2
====
