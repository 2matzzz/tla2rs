---- MODULE ActStep ----
\* When TLC checks [][A]_v: on every successor, after a new one is added and its invariants are
\* checked, and also on successors outside the CONSTRAINT. A violation exits with 13; a failed
\* evaluation reports "Evaluating action property ... failed" with the behavior up to the
\* successor (exit 255 for \div, 75 for anything else)
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x # 2
Con == x < 2
Up == [][x' # 2]_x
UpEval == [][x' = 2 => 1 \div (x - x) = 0]_x
UpCase == [][x' = 2 => (CASE x = 7 -> TRUE)]_x
====
