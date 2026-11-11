---- MODULE RejSanyPrecUser ----
\* Two user-defined operators of the same precedence range need parentheses too
EXTENDS Naturals
VARIABLE x
a ?? b == a + b
a !! b == a * b
Init == x = 0
Next == x' = (x ?? 1 !! 2) % 3
====
