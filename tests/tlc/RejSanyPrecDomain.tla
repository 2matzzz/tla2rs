---- MODULE RejSanyPrecDomain ----
\* DOMAIN and an infix operator of the ranges 10 to 13 after its operand need parentheses
EXTENDS Naturals
VARIABLE x
Size == DOMAIN <<1>> + 1
Init == x = 0
Next == x' = (x + 1) % 3
====
