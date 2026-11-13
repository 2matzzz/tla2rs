---- MODULE RejSanyMany ----
\* SANY reports every error of a module in the order it meets them, then its warnings
EXTENDS Naturals
VARIABLE x
Pick == \E x \in {1} : TRUE
Pick == 2
Twice == y + z
Pairs == 1 @@ (2 @@ 3)
Init == x = 0
Next == x' = (x + 1) % 3
====
