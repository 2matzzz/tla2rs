---------------------------- MODULE OrDup ----------------------------
(* An action with a \/ whose branches can both be true. TLC counts successors per \/ branch, so it
   counts the same successor twice (its "states generated" exceeds tla2rs's).
   Distinct state counts and verdicts match. *)
EXTENDS Naturals

VARIABLE x

TypeOK == x \in 0..3
Init == x = 0

\* Both branches are true for x = 0 and 1
Step == (x < 3 \/ x < 2) /\ x' = x + 1

\* The same happens inside \A
Both == \A i \in {1} : (x < 3 \/ x < 2)
Step2 == Both /\ x' = x + 1

Next == Step
Next2 == Step2

Inv == x <= 3
=============================================================================
