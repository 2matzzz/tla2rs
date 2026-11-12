---- MODULE InstLetInner ----
\* A definition called from a LET definition, in a module that InstLet instantiates
EXTENDS Naturals
VARIABLE tally
Wrap(v) == [val |-> v, half |-> v \div 2]
Bump == tally < 4 /\ tally' = LET next == Wrap(tally + 1) IN next.val
====
