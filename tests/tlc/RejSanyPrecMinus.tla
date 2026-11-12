---- MODULE RejSanyPrecMinus ----
\* Unary minus may not be the operand of an operator that binds tighter
EXTENDS Integers
VARIABLE x
Neg == 2 * -x
Init == x = 0
Next == x' = (x + 1) % 3
====
