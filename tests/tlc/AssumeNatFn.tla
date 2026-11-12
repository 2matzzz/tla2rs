---- MODULE AssumeNatFn ----
\* ASSUMEs over sets built from Nat: a recursive function over Nat \X S (TLC tests membership in
\* the product component by component) and \subseteq a set made from Nat, neither built
EXTENDS Naturals, FiniteSets
Steps(S, start) ==
  LET reach[n \in Nat, v \in S] ==
        IF n = 0 THEN v = start
                 ELSE reach[n - 1, v] \/ \E u \in S : reach[n - 1, u] /\ (u + 1 = v)
  IN {v \in S : reach[Cardinality(S), v]}
ASSUME Steps(1..4, 2) = 2..4
ASSUME \A k \in 0..3 : Cardinality(Steps(0..k, 0)) = k + 1
ASSUME (1..3) \subseteq Nat \ {0}
ASSUME ~((0..3) \subseteq Nat \ {0})
VARIABLE x
Init == x = 0
Next == x' = 1 - x
====
