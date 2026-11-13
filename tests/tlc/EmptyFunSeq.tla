---- MODULE EmptyFunSeq ----
\* A function over a constant empty domain is the empty function, which is the empty sequence
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = <<TRUE>>
Next == x' = LET t == [i \in 1..0 |-> x[1]] IN IF Len(t) < Len(x) THEN t ELSE Append(t, TRUE)
====
