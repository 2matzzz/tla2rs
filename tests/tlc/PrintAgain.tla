---- MODULE PrintAgain ----
\* After an evaluation error while checking a new state, TLC evaluates again to report where the
\* error is, printing again. For a successor that fails an invariant: after the behavior, it
\* generates every successor of the state it was expanding once more (the actions print in
\* order), adds and queues those it has not seen (counted as distinct and left on queue), and
\* checks their invariants, up to the first that fails; one that fails to evaluate again makes it
\* exit with 255. For an error while computing or checking the initial states: it computes and
\* checks them again from the start, up to the error
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1, 2} /\ PrintT(<<"init", x>>)
InitErr == x \in {0, 1, 2} /\ PrintT(<<"init", x>>) /\ 1 \div (1 - x) >= 0
A == x < 9 /\ PrintT(<<"A", x>>) /\ x' = x + 1
B == x < 9 /\ PrintT(<<"B", x>>) /\ x' = x + 2
C == x < 9 /\ PrintT(<<"C", x>>) /\ x' = x + 10
D == x < 9 /\ PrintT(<<"D", x>>) /\ x' = x + 20
Next == A \/ B \/ C \/ D
Spec == Init /\ [][Next]_x
Ok == PrintT(<<"ok", x>>)
Bad == PrintT(<<"bad", x>>) /\ 1 \div (4 - x) >= 0
BadTwice == PrintT(<<"bad", x>>) /\ 1 \div ((4 - x) * (22 - x)) >= 0
BadInit == PrintT(<<"bad", x>>) /\ 1 \div (1 - x) >= 0
Cons == PrintT(<<"cons", x>>) /\ 1 \div (2 - x) >= 0
Live == <>(x = 100)
====
