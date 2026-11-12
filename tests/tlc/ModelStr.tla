---- MODULE ModelStr ----
\* TLC orders a model value before any string: in a set, in the domain of a function, and for CHOOSE
EXTENDS TLC
CONSTANT Ms
VARIABLE f, pick
Keys == Ms \cup {"zz", "aa"}
Init == f = [k \in Keys |-> 0] /\ pick = CHOOSE k \in Keys : TRUE
Next == \E k \in Keys : f[k] = 0 /\ f' = [f EXCEPT ![k] = 1] /\ pick' = k
ASSUME PrintT(Keys)
Few == \E k \in Keys : f[k] = 0
====
