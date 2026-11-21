---- MODULE ExceptKeyEmptyFun ----
\* An EXCEPT key that is no integer on the empty function: TLC has no element of the domain to
\* compare it with, so the EXCEPT changes nothing and warns (issue #123). Apart from ExceptKey,
\* which builds empty tuples: a spec that builds both is not followed
EXTENDS Naturals, TLC
VARIABLE x
Init == x = [i \in {} |-> 1]
Next == x' = [x EXCEPT !["a"] = 9]
====
