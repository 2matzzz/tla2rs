---- MODULE BigConstErr ----
\* TLC builds the set CHOOSE chooses from (but SUBSET S) and the set {e : x \in S} goes through,
\* and stops when it has more than a million elements
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Which
VARIABLE x
ASSUME Which = "choose" => PrintT(CHOOSE t \in (1..100) \X (1..100) \X (1..200) : t[1] = 2)
ASSUME Which = "chooserec" => PrintT(CHOOSE r \in [a : 1..1000, b : 1..1001] : r.a = 2)
ASSUME Which = "choosefun" => PrintT(CHOOSE f \in [1..20 -> 1..3] : TRUE)
ASSUME Which = "map" => PrintT({Cardinality(s) : s \in SUBSET (1..21)})
ASSUME Which = "mapfilter" => PrintT({f[1] : f \in {g \in [1..20 -> 1..2] : g[2] = 2 /\ \A i \in 3..20 : g[i] = 1}})
Init == x = 0
Next == x' = x
====
