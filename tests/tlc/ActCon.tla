---- MODULE ActCon ----
\* ACTION_CONSTRAINT(S): like CONSTRAINT, on the step from a state to its successor. A step that
\* violates it is counted as generated, not added, and its target's invariants are still checked.
\* TLC accepts TYPE and TYPE_CONSTRAINT and does nothing with them
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
Inv == x # 2
NotTwo == x' # 2
NotThree == x' # 3
====
