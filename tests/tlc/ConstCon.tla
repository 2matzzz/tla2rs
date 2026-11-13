---- MODULE ConstCon ----
\* A constraint or action constraint of constant level is evaluated before exploring, as an
\* invariant is: TLC stops if it is not TRUE
EXTENDS Naturals
CONSTANT N
VARIABLE x
Init == x = 0
Next == x' = 1 - x
CF == N > 5
CT == N > 1
CN == N
====
