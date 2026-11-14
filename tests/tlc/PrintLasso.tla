---- MODULE PrintLasso ----
\* To show a liveness counterexample, TLC rebuilds its states from fingerprints, evaluating Init
\* (all of it) and the steps again: first the steps up to the state the cycle starts at, before it
\* shows any state, then each step of the cycle just before the state it leads to, and the step
\* back to the start of the cycle before `Back to state`. Each step evaluates the actions in order
\* up to the one that yields the next state
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1} /\ PrintT(<<"init", x>>)
A == x < 3 /\ PrintT(<<"A", x>>) /\ x' = x + 1
B == x = 3 /\ PrintT(<<"B", x>>) /\ x' = 2
C == x = 2 /\ PrintT(<<"C", x>>) /\ x' = 0
D == x < 2 /\ PrintT(<<"D", x>>) /\ x' = x + 1
Back == A \/ B
Ring == D \/ C
SpecBack == Init /\ [][Back]_x /\ WF_x(Back)
SpecRing == Init /\ [][Ring]_x /\ WF_x(D)
SpecStop == Init /\ [][Back]_x
Inv == PrintT(<<"inv", x>>)
Cycle == <>[](x = 3)
Zero == []<>(x = 0)
Never == <>(x = 7)
====
