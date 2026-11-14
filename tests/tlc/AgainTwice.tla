---- MODULE AgainTwice ----
\* With -continue, a successor that fails to evaluate an invariant again, in the pass TLC makes
\* after showing the behavior (see AgainCount), is reported as a failed invariant with its
\* behavior, then as the error with the behavior again (PrintAgain-TwiceContinue, without printing)
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1, 2}
Next == x < 9 /\ x' \in {x + 1, x + 2, x + 10, x + 20}
Spec == Init /\ [][Next]_x
BadTwice == 1 \div ((4 - x) * (22 - x)) >= 0
Live == <>(x = 100)
====
