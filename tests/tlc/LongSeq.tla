---- MODULE LongSeq ----
\* DOMAIN of a sequence that can be longer than 128
EXTENDS Naturals, Sequences, FiniteSets
VARIABLE q
Init == q = <<>>
Next == q' = IF Len(q) < 140 THEN Append(q, Len(q) % 2) ELSE q
Inv == Cardinality(DOMAIN q) = Len(q) /\ (Len(q) > 0 => Len(q) \in DOMAIN q)
====
