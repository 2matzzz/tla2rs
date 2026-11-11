---- MODULE RejSanyMinus ----
\* Unary minus is defined in Integers: SANY refuses it in a module that extends only Naturals
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = -x
====
