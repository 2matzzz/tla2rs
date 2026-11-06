---- MODULE ChooseStr ----
VARIABLE x
TypeOK == x \in {"b", "a"}
Init == x = CHOOSE v \in {"b", "a"} : TRUE
Next == UNCHANGED x
Inv == x = "a"
====
