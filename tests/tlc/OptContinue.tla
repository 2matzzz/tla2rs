---- MODULE OptContinue ----
\* TLC's -continue: the search goes on past each violated invariant, reporting every one
EXTENDS Naturals
VARIABLES x, y
TypeOK == x \in 0..3 /\ y \in 0..3
Init == x \in {0, 2} /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ y' = y
        \/ y < 2 /\ y' = y + 1 /\ x' = x
NotTwo == x # 2
NotThree == x + y # 3
====
