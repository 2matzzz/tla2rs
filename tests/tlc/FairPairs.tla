---- MODULE FairPairs ----
\* Fairness on each pair of distinct processes, written with a constant guard: TLC takes the guard
\* as TRUE or FALSE, so these are fairness conditions, which the property needs. In the property's
\* automaton instead they made it grow beyond 4096 states
EXTENDS Naturals
CONSTANT P
VARIABLE met
Init == met = {}
Meet(i, j) == /\ <<i, j>> \notin met
              /\ met' = met \cup {<<i, j>>}
Next == \E i, j \in P : i # j /\ Meet(i, j)
Spec == Init /\ [][Next]_met /\ \A i, j \in P : i # j => WF_met(Meet(i, j))
AllMet == \A i, j \in P : i # j => <>(<<i, j>> \in met)
====
