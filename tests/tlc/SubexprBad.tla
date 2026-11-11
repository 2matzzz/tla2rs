---- MODULE SubexprBad ----
\* SANY refuses a subexpression of CASE named by one position only (TLC stops with exit 150)
EXTENDS Naturals
VARIABLE x
Cs == CASE x = 0 -> 10 [] OTHER -> 30
Init == x = 0
Next == x' = (x + 1) % 2
Inv == Cs!1 = 10
====
