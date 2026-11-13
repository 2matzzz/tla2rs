---- MODULE DomainStr ----
\* "k" \in DOMAIN f for a function f over strings
EXTENDS Naturals
VARIABLES f
TypeOK == f \in [{"s", "t"} -> 0..2]
Init == f = [k \in {"s", "t"} |-> 0]
Next == /\ f["s"] < 2
        /\ f' = [f EXCEPT !["s"] = @ + 1]
        /\ "s" \in DOMAIN f
        /\ "b" \notin DOMAIN f
====
