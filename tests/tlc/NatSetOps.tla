---- MODULE NatSetOps ----
\* Membership of a constant in sets built from Nat and Int with \, \cup, \cap and a filter, which
\* TLC tests without building the set
EXTENDS Integers
CONSTANT N, M
ASSUME N \in Nat \ {0}
ASSUME M \in {k \in Nat : k % 2 = 0} \cup {7}
ASSUME N \notin Int \cap {-5, -6}
VARIABLE x
Init == x = 0
Next == x < N /\ x' = x + 1
Spec == Init /\ [][Next]_x
====
