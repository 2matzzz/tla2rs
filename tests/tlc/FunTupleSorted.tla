---- MODULE FunTupleSorted ----
\* A function over keys that are not all integers tested for membership in a sorted set of tuples
\* (from a definition or the state): TLC searches the set with its order, comparing the function
\* with each element it visits by size, then key by key, and stops at a key that is not an integer
EXTENDS Naturals, TLC
CONSTANT m
VARIABLES n, s, f
Trio == {<<1>>, <<2>>, <<3>>}
Pairs == {<<1, 1>>, <<2, 2>>, <<3, 3>>}
\* Tuples of several lengths: the search meets <<1, 2>> first
Lens == {<<1>>, <<1, 2>>, <<1, 2, 3>>}
\* The search passes <<3>> and <<1, 2, 3>> and never meets a tuple of two elements
Gap == {<<1>>, <<2>>, <<3>>, <<1, 2, 3>>}
Init == n = 0 /\ s = Trio /\ f = ("a" :> 1)
InitIn == n = 0 /\ ("a" :> n) \notin Trio /\ s = Trio /\ f = ("a" :> 1)
Next == n < 2 /\ n' = n + 1 /\ s' = s \cup {<<n + 4>>} /\ UNCHANGED f
NextIn == n < 2 /\ n' = n + 1 /\ (n = 1 => ("a" :> n) \notin s) /\ s' = s \cup {<<n + 4>>} /\ UNCHANGED f
InStr == n = 1 => ("a" :> n) \notin Trio
InModel == n = 1 => (m :> n) \notin Trio
InLambda == n = 1 => [k \in {"a"} |-> n] \notin Trio
\* Keys in TLC's order of strings, the order it first meets them
InOrder == n = 1 => ("z" :> n @@ "y" :> 2) \notin Pairs
\* m sorts before the integer key
InMix == n = 1 => (1 :> 1 @@ m :> n) \notin Pairs
\* Sizes differ from every element: no error
InSize == ("a" :> n @@ "b" :> 1) \notin Trio
InState == n = 1 => f \notin s
InLens == n = 1 => ("a" :> n @@ "b" :> 1) \notin Lens
InGap == ("a" :> n @@ "b" :> 1) \notin Gap
\* Integer keys compare with the indices
InInt == n = 1 => ((1 :> 5) \notin Trio /\ [i \in 1..2 |-> n] \notin Pairs)
====
