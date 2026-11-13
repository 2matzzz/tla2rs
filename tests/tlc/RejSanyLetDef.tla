---- MODULE RejSanyLetDef ----
\* A LET definition may not reuse a parameter's name; one repeated in the same LET is refused, and warned about
EXTENDS Naturals
VARIABLE x
Shift(a) == LET a == 1 IN a + q
Twice == LET b == 1 b == 2 IN b
Init == x = 0
Next == x' = (x + 1) % 3
====
