---- MODULE LiveFold ----
\* Liveness under a VIEW or a SYMMETRY, where TLC's liveness graph is not the folded state graph:
\* TLC keeps each successor as generated (two successors with the same view are two steps, and a
\* successor with the view of the state itself is a step beside the stuttering one), checks the
\* tableau on the successor itself, and adds a step into a state already expanded only once
EXTENDS Naturals, TLC
CONSTANT P
VARIABLES x, y
vars == <<x, y>>
View == y
Sym == Permutations(P)

\* Turn changes only what the view leaves out: its steps are self-loops of the folded graph, which
\* TLC counts as steps of Turn, so weak fairness of Turn holds while y stays 0
Init == x = 0 /\ y = 0
Turn == x' = 1 - x /\ UNCHANGED y
Flip == y' = 1 - y /\ UNCHANGED x
Spec == Init /\ [][Turn \/ Flip]_vars /\ WF_vars(Turn)
OftenOne == []<>(y = 1)
SomeOne == <>(y = 1)

\* The same under a SYMMETRY: Swap moves x to the other model value
SInit == x = (CHOOSE p \in P : TRUE) /\ y = 0
Swap == x' = (CHOOSE p \in P : p # x) /\ UNCHANGED y
SSpec == SInit /\ [][Swap \/ Flip]_vars /\ WF_vars(Swap)

\* Flip0 and Flip1 reach the same view. TLC checks the tableau of NotOne on the successor Flip1
\* makes, which keeps x = 1, although the state the graph keeps for that view has x = 0
TInit == x = 1 /\ y = 0
Flip0 == y' = 1 - y /\ x' = 0
Flip1 == y' = 1 - y /\ x' = x
Up == y' = 1 - y /\ x' = 1
TSpec == TInit /\ [][Flip0 \/ Flip1 \/ Up]_vars /\ WF_vars(Flip0 \/ Flip1 \/ Up)
NotOne == <>(x # 1)

\* From y = 1, Back and Go both return to the view of the initial state, expanded already. TLC
\* keeps only the step it put first into its set of successors, so strong fairness of Go cannot
\* hold on that cycle when Back comes first (DSpec) and can when Go does (DSpecGo)
Back == y' = 1 - y /\ x' = x
Go == y = 1 /\ y' = 0 /\ x' = 1 - x
DSpec == Init /\ [][Back \/ Go]_vars /\ WF_vars(Back) /\ SF_vars(Go)
DSpecGo == Init /\ [][Go \/ Back]_vars /\ WF_vars(Back) /\ SF_vars(Go)
Settles == <>[](y = 1)

\* Fall returns to the view of the initial state with x = 1. A node of the tableau new to a state
\* expanded already gets its transitions and its ENABLED from the successor that made it, here
\* Fall's, where Fin is disabled, so weak fairness of Fin holds on the cycle through such nodes
Rise == y = 0 /\ y' = 1 /\ x' = x
Fall == y = 1 /\ y' = 0 /\ x' = 1
Fin == x = 0 /\ y # 2 /\ y' = 2 /\ x' = x
LSpec == Init /\ [][Rise \/ Fall \/ Fin]_vars /\ WF_vars(Fin)
Reaches == (y = 1) ~> (y = 2)
====
