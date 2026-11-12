---- MODULE InstDomInner ----
\* Instantiated by InstDom: Node is a constant set, although its definition there takes the
\* module's variable as an argument
EXTENDS Naturals
CONSTANT N
VARIABLE flag
Node == 1..N
Init == flag \in [Node -> BOOLEAN]
Next == \E n \in Node : flag[n] /\ flag' = [flag EXCEPT ![n] = FALSE]
TypeOK == flag \in [Node -> BOOLEAN]
====
