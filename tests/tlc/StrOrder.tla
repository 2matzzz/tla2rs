---- MODULE StrOrder ----
VARIABLE x
TypeOK == x \in {"z", "b", "a"}
Init == x = "z"
Next == x' \in {"b", "a"}
Inv == x # "a"
====
