---- MODULE IntTupleIn ----
\* An integer tested for membership in a set of tuples: a set written out asks each element whether
\* it equals the integer, a sorted set (from a definition or the state) compares the integer with
\* the element it visits first
EXTENDS Naturals
VARIABLES n, x, s
Trio == {<<1>>, <<2>>, <<3>>}
Init == n = 0 /\ x = 1 /\ s = Trio
InitIn == n = 0 /\ x = 1 /\ s = Trio /\ x \notin {<<1>>}
Next == n < 2 /\ n' = n + 1 /\ UNCHANGED <<x, s>>
NextIn == n < 2 /\ n' = n + 1 /\ (n = 1 => x \notin {<<1>>}) /\ UNCHANGED <<x, s>>
InLit == n = 1 => x \in {<<1>>}
InFirst == x \notin {<<1>>}
InTrio == n = 1 => x \notin Trio
InState == n = 1 => x \notin s
====
