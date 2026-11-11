---- MODULE MCSubst ----
\* Model values and definitions that the cfg substitutes for the constants of Subst
EXTENDS Subst
CONSTANTS p1, p2, i1, i2, i3
MCProcs == {p1, p2}
MCItems == {i1, i2, i3}
MCOwner == [i \in MCItems |-> IF i = i1 THEN p1 ELSE p2]
MCConf == [shared |-> FALSE, max |-> 2]
MCConfShared == [MCConf EXCEPT !.shared = TRUE]
\* Refers to a constant that is itself substituted
MCLimit == Cardinality(Items) + 1
MCCap == 2
====
