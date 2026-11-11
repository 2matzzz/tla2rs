---- MODULE LongerSeq ----
\* A sequence of 300 elements
EXTENDS Integers, Sequences
VARIABLE q
Init == q = <<>>
Next == \/ Len(q) < 300 /\ q' = Append(q, Len(q) % 3)
        \/ Len(q) = 300 /\ UNCHANGED q
Inv == Len(q) <= 300 /\ (Len(q) > 0 => q[Len(q)] = (Len(q) - 1) % 3)
====
