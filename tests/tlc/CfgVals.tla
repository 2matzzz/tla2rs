---- MODULE CfgVals ----
\* Constant values TLC accepts in a cfg: natural numbers, strings, booleans, model values, and sets
\* of these, nested to any depth (TLC rejects negative numbers, tuples, records and ranges)
EXTENDS Naturals, FiniteSets
CONSTANTS Groups, Nums, Deep, Flag, Name
VARIABLE g
Init == g \in Groups
Next == g' \in Groups
Inv == /\ Cardinality(g) <= 2
       /\ \A s \in Nums : Cardinality(s) >= 1
       /\ \A s \in Deep : \A t \in s : Cardinality(t) = 1
       /\ Flag
       /\ Name = "n"
       /\ Cardinality(g) # 2
====
