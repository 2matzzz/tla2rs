---- MODULE RejSanyPostfix ----
\* UNCHANGED and a prime on its operand need parentheses
EXTENDS Naturals
VARIABLE x
Same == UNCHANGED x'
Init == x = 0
Next == x' = (x + 1) % 3
====
