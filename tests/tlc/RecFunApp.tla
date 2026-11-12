---- MODULE RecFunApp ----
\* A recursive function whose value at n is a function built by applying its value at n - 1 (the
\* reachability relation in at most n steps), applied in an invariant to a relation from the state
EXTENDS Naturals, FiniteSets
CONSTANT Pts
VARIABLE link
Closure(L) ==
  LET within[n \in Nat] ==
        [p, q \in Pts |-> IF n = 0 THEN <<p, q>> \in L
                          ELSE \/ within[n - 1][p, q]
                               \/ \E r \in Pts : within[n - 1][p, r] /\ within[n - 1][r, q]]
  IN within[Cardinality(Pts)]
Init == link = {}
Next == \E p, q \in Pts : p /= q /\ <<p, q>> \notin link /\ link' = link \cup {<<p, q>>}
NoCycle == LET c == Closure(link) IN \A p \in Pts : ~c[p, p]
\* The same over a function passed as an argument (its code applied where it is written)
Same == [p, q \in Pts |-> p = q]
Within(F, S, n) ==
  LET w[k \in Nat] ==
        [p, q \in S |-> IF k = 0 THEN F[p, q]
                        ELSE w[k - 1][p, q] \/ \E r \in S : w[k - 1][p, r] /\ w[k - 1][r, q]]
  IN w[n]
Bounded == \A p, q \in Pts : Within(Same, Pts, 2)[p, q] => p = q
====
