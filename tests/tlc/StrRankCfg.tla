---- MODULE StrRankCfg ----
\* The strings of the cfg come first of all, in cfg order
CONSTANT S
VARIABLE x
Other == "p"
Init == x = "start"
Next == x' \in S
Inv == x # "q"
====
