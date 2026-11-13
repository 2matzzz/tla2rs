---- MODULE RejSanyDefVar ----
\* A definition named like a VARIABLE is refused before its body and after it; a function definition only before
EXTENDS Naturals
VARIABLE x, f
x == y
f[i \in {1}] == q
Init == x = 0
Next == x' = (x + 1) % 3
====
