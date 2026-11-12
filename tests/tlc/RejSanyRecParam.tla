---- MODULE RejSanyRecParam ----
\* A RECURSIVE declaration puts the name in scope: a parameter may not reuse it
EXTENDS Naturals
VARIABLE x
RECURSIVE Down(_)
Apply(Down) == Down
Down(n) == IF n = 0 THEN 0 ELSE Down(n - 1)
Init == x = 0
Next == x' = (x + 1) % 3
====
