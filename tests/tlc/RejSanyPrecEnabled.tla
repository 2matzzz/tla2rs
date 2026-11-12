---- MODULE RejSanyPrecEnabled ----
\* ENABLED and an infix operator after its operand need parentheses
EXTENDS Naturals
VARIABLE x
Can == ENABLED x' = 1
Init == x = 0
Next == x' = (x + 1) % 3
====
