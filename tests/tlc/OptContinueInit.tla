---- MODULE OptContinueInit ----
\* With -continue TLC reports every invariant an initial state violates, a successor only the first
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1}
Next == x' = (x + 1) % 3
A == x # 1
B == x < 1
C == x < 2
====
