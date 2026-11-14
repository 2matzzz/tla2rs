---- MODULE AgainCount ----
\* After a successor fails to evaluate an invariant, TLC generates the successors of the state it
\* was expanding once more to report where the error is, and adds and queues those it has not
\* seen: they count as distinct and left on queue (see PrintAgain for what it prints then)
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1, 2}
Next == x < 9 /\ x' \in {x + 1, x + 2, x + 10, x + 20}
Bad == 1 \div (4 - x) >= 0
====
