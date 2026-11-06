---------------------------- MODULE Liveness ----------------------------
(* For testing liveness checking. x cycles 0 -> 1 -> 2 -> 0, and y is set nondeterministically.
   If Fair is TRUE, Step gets weak fairness. *)
EXTENDS Naturals

CONSTANT Fair

VARIABLES x, y

TypeOK == x \in 0..2 /\ y \in BOOLEAN

Init == x = 0 /\ y = FALSE

Step == x' = (x + 1) % 3 /\ UNCHANGED y
Flip == y' = ~y /\ UNCHANGED x

Next == Step \/ Flip

Spec == Init /\ [][Next]_<<x, y>> /\ WF_<<x, y>>(Step)
SpecNoFair == Init /\ [][Next]_<<x, y>>

ReachTwo == <>(x = 2)
InfOftenZero == []<>(x = 0)
EventuallyStable == <>[](x = 1)
LeadsTo == (x = 1) ~> (x = 0)
YEventually == <>y
=============================================================================
