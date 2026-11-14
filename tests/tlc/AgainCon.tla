---- MODULE AgainCon ----
\* After the CONSTRAINT, the ACTION_CONSTRAINT or the VIEW fails to evaluate on a successor, TLC
\* reports the error without a behavior and then generates the successors of the state it was
\* expanding once more, as after an invariant that fails to evaluate (see PrintAgain): the actions
\* and the constraints print again in order, the invariants of a successor outside the constraints
\* are checked again, up to the error
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1} /\ PrintT(<<"init", x>>)
A == x < 9 /\ PrintT(<<"A", x>>) /\ x' = x + 1
B == x < 9 /\ PrintT(<<"B", x>>) /\ x' = x + 2
C == x < 9 /\ PrintT(<<"C", x>>) /\ x' = x + 10
Next == C \/ A \/ B
Spec == Init /\ [][Next]_x
Cons == PrintT(<<"cons", x>>) /\ 1 \div (4 - x) >= 0 /\ x < 10
ActCons == PrintT(<<"act", x, x'>>) /\ 1 \div (4 - x') >= 0 /\ x' < 10
Inv == PrintT(<<"inv", x>>)
View == IF x = 4 THEN 1 \div (x - x) ELSE x
Live == <>(x = 100)
InitQ == x \in {0, 1}
NextQ == x < 9 /\ x' \in {x + 10, x + 1, x + 2}
ConsQ == 1 \div (4 - x) >= 0 /\ x < 10
====
