---- MODULE HugeSeq ----
\* A sequence of 3000 elements (each state holds it inline)
EXTENDS Integers, Sequences
VARIABLE q
TypeOK == q \in Seq(0..2) /\ Len(q) <= 3000
Init == q = <<>>
Next == \/ Len(q) < 3000 /\ q' = Append(q, Len(q) % 3)
        \/ Len(q) = 3000 /\ UNCHANGED q
Inv == Len(q) > 0 => q[Len(q)] = (Len(q) - 1) % 3
\* Violated
Short == Len(q) < 2999
====
