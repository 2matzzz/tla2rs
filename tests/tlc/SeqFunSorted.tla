---- MODULE SeqFunSorted ----
\* A sequence tested for membership in a sorted set of functions over keys that are not all
\* integers: TLC searches the set as for a tuple, by size, then key by key
EXTENDS Naturals, Sequences, TLC
VARIABLES n, q
Trio == {("a" :> 1), ("b" :> 1), ("c" :> 1)}
Pairs == {("a" :> 1 @@ "b" :> 1), ("c" :> 1 @@ "d" :> 1)}
Init == n = 0 /\ q = <<>>
Next == n < 2 /\ n' = n + 1 /\ q' = Append(q, n)
InTrio == n = 1 => Append(Tail(q), n) \notin Trio
InPairs == Append(q, 1) \notin Pairs
InState == q \notin Trio
====
