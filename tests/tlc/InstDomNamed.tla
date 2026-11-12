---- MODULE InstDomNamed ----
\* A function over a constant set defined in a named instance, whose definitions take the
\* instance's variable as an argument
EXTENDS Naturals
CONSTANT N
VARIABLE flag, seen
Inner == INSTANCE InstDomInner
Init == Inner!Init /\ seen = [n \in Inner!Node |-> 0]
Next == \E n \in Inner!Node : seen[n] < 2 /\ seen' = [seen EXCEPT ![n] = @ + 1] /\ UNCHANGED flag
TypeOK == seen \in [Inner!Node -> 0..2]
====
