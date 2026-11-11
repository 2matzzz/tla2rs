---- MODULE OpConst ----
\* CONSTANTs with parameters, given by the cfg
EXTENDS Naturals
CONSTANTS Nodes, Weight(_), Combine(_, _), Bonus(_)
VARIABLES total, last
TypeOK == total \in 0..9 /\ last \in Nodes \cup {"none"}
Init == total = 0 /\ last = "none"
Next == \E n \in Nodes :
          /\ total' = Combine(total, Weight(n) + Bonus(n))
          /\ last' = n
Inv == total < 9
====
