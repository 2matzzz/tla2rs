---- MODULE SeqHead ----
\* Head of the empty sequence is an evaluation error, and so is a tuple index out of range
EXTENDS Naturals, Sequences
VARIABLES q, k
TypeOK == q \in Seq(1..2) /\ k \in 0..4
Init == q = <<1, 2>> /\ k = 1
Next == /\ q' = Tail(q)
        /\ k' = k + 1
        /\ Head(q) > 0
        /\ <<5, 6, 7>>[k] > 0
Bound == Len(q) <= 2
====
