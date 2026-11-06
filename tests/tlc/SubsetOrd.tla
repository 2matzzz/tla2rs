---- MODULE SubsetOrd ----
VARIABLE s, k
TypeOK == s \in SUBSET {0, 1, 2} /\ k \in BOOLEAN
Init == s = {} /\ k = FALSE
Next == ~k /\ s' \in SUBSET {0, 1, 2} /\ k' = TRUE
Inv == s # {1}
====
