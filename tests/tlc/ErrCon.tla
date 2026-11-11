---- MODULE ErrCon ----
\* An error while evaluating the CONSTRAINT, the ACTION_CONSTRAINT or the VIEW. On a successor TLC
\* stops with an unexpected exception and shows no behavior; the successor counts as generated but
\* not as distinct. The exit code is 255 for \div and 75 for anything else. On an initial state it
\* is reported like any error in the initial states (exit 75)
EXTENDS Naturals
VARIABLE x
Init == x = 0
InitAll == x \in 0..3
Next == x < 3 /\ x' = x + 1
Stay == x' = x
Con == x = 2 => 1 \div (x - x) = 0
ConCase == x = 2 => (CASE x = 7 -> TRUE)
ACon == x' = 2 => 1 \div (x - x) = 0
View == IF x = 2 THEN (IF 1 \div (x - x) = 0 THEN 1 ELSE 2) ELSE x
====
