---- MODULE NoActions ----
\* A next-state relation that TLC splits into no action (\E over an empty set): TLC computes and
\* checks the initial states and stops (exit 75). One of constant level given as NEXT is refused
\* when TLC reads the spec (exit 151); [][FALSE]_x in a SPECIFICATION deadlocks
EXTENDS Naturals, TLC
VARIABLE x
C == PrintT("constant")
ASSUME PrintT("assume")
Init == PrintT("init") /\ x = 0
Next == \E i \in {} : x' = i
NextFalse == FALSE
NextEq == 1 = 2
NextLet == LET S == {} IN \E i \in S : x' = i
NextOr == (\E i \in {} : x' = i) \/ (\E j \in 1..0 : x' = j)
Spec == Init /\ [][FALSE]_x
SpecEmpty == Init /\ [][\E i \in {} : x' = i]_x
Inv == x < 5
InvBad == x > 0
====
