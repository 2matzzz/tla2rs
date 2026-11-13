---- MODULE SubLet ----
\* Positional names of LET definitions, with and without arguments, in an action
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == /\ LET M == x < 5 /\ x >= 0 IN M!1
        /\ LET N(a) == a + 1 IN x' = (N(1)!1 + x) % 3
====
