---- MODULE RecOrder ----
EXTENDS Integers, TLC
\* TLC compares records field by field in the order it first created the field names (zeta
\* here, before mu), which decides CHOOSE over a set of records
zeta == 1
VARIABLE x, c
Init == x \in {0, 1} /\ c = CHOOSE r \in {[mu |-> x, zeta |-> 1 - x], [mu |-> 1 - x, zeta |-> x]} : TRUE
Next == UNCHANGED <<x, c>>
Inv == c.zeta = 0
ConstInv == (CHOOSE r \in {[mu |-> 0, zeta |-> 1], [mu |-> 1, zeta |-> 0]} : TRUE).zeta = 0
====
