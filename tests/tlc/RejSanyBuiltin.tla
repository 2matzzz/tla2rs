---- MODULE RejSanyBuiltin ----
\* BOOLEAN is always in scope: a bound variable may not reuse it
EXTENDS Naturals
VARIABLE x
Any2 == \E BOOLEAN \in {1} : TRUE
Init == x = 0
Next == x' = (x + 1) % 3
====
