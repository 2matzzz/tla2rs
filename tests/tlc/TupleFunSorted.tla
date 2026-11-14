---- MODULE TupleFunSorted ----
\* A tuple tested for membership in a sorted set (from a definition or the state) of functions over
\* keys that are not all integers: TLC searches the set with its order, starting in the middle
EXTENDS Naturals, TLC
CONSTANT m
VARIABLES n, s
Trio == {("a" :> 1), ("b" :> 1), ("c" :> 1)}
Quad == {("a" :> 1), ("b" :> 1), ("c" :> 1), ("d" :> 1)}
\* m sorts before integers: the search goes left of (2 :> 1) and fails on (m :> 1)
Deep == {(m :> 1), (2 :> 1), (3 :> 1)}
\* The search goes right of (0 :> 1) and never meets (m :> 1)
Skip == {(m :> 1), (0 :> 1)}
Init == n = 0 /\ s = Trio
Next == n < 2 /\ n' = n + 1 /\ s' = s \cup {("d" :> n), ("e" :> n)}
InTrio == n = 1 => <<n>> \notin Trio
InQuad == n = 1 => <<n>> \notin Quad
InDeep == n = 1 => <<n>> \notin Deep
InSkip == <<n>> \notin Skip
InSize == <<n, 1>> \notin Trio
InState == n = 2 => <<1>> \notin s
====
