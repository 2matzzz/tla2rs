---- MODULE RejSanyFunName ----
\* The name of a function definition is in scope in its bound variable and body
EXTENDS Naturals
VARIABLE x
f[f \in {1, 2}] == 0
Init == x = 0
Next == x' = (x + 1) % 3
====
