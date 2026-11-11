---- MODULE RejSanyPrec ----
\* SANY refuses operators of overlapping precedence next to each other without parentheses (TLC stops with exit 150)
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Mixed == x = 0 /\ x < 2 \/ x = 2
====
