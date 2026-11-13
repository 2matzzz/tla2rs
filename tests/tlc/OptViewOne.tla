---- MODULE OptViewOne ----
\* TLC's -view prints a VIEW <<x>> of a spec of one variable as a state, with its /\
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Small == x < 2
View == <<x>>
====
