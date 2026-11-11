---- MODULE ZeroState ----
\* A successor whose packed bits are all zero (x = 0 first reached after the initial state)
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..2
Init == x = 1
Next == x' = IF x = 1 THEN 0 ELSE x
Inv == x # 0
====
