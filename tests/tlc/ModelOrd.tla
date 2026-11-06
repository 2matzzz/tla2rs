---- MODULE ModelOrd ----
CONSTANTS P, q
VARIABLE x
TypeOK == x \in P \cup {q}
Init == x = CHOOSE p \in P : TRUE
Next == x' \in P \cup {q}
Inv == x # q /\ x # "q"
====
