---- MODULE RejSanySubexpr ----
\* SANY checks the positional subexpression names of every definition, used or not
EXTENDS Naturals
VARIABLE x
Sum == x + 1
Third == Sum!3
Init == x = 0
Next == x' = (x + 1) % 3
====
