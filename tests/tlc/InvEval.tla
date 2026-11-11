---- MODULE InvEval ----
\* An invariant that fails to evaluate. TLC reports "Evaluating invariant Inv failed", shows the
\* behavior up to and including the state it failed on, and exits with 76 whatever the error. In an
\* initial state it shows only the counts and exits with 75. On a state outside the CONSTRAINT
\* (not counted as distinct) it exits with the error's own code: 255 for \div, 75 for CASE
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
InitAll == x \in 0..3
Next == x < 3 /\ x' = x + 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Inv == x = 2 => 1 \div (x - x) = 0
InvCase == x = 2 => (CASE x = 7 -> TRUE)
Con == x < 2
Prop == <>(x = 3)
====
