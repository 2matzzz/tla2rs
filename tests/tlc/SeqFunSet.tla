---- MODULE SeqFunSet ----
\* [1..n -> S] with n from the state: its functions are sequences, which \o can join
EXTENDS Naturals, Sequences, FiniteSets
VARIABLE q
Init == q = <<>>
Next == \E s \in UNION {[1..m -> {"a", "b"}] : m \in 1..(3 - Len(q))} : q' = q \o s
Count == Cardinality([1..Len(q) -> {1, 2}]) = 2^Len(q)
====
