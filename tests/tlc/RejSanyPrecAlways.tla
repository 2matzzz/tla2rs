---- MODULE RejSanyPrecAlways ----
\* [] and an infix operator after its operand need parentheses (TLC stops with exit 150)
EXTENDS Naturals
VARIABLE x
Prop == []x < 3
Init == x = 0
Next == x' = (x + 1) % 3
====
