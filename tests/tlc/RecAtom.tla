---- MODULE RecAtom ----
\* A variable holding records of different fields and a model value in one function (and a tuple
\* with either): the type invariant lists them, and is checked on each state
EXTENDS Naturals
CONSTANT Keys, None
VARIABLE slot, last
Reqs == [kind : {"get"}, key : Keys] \cup [kind : {"put"}, key : Keys, val : 0..1]
TypeOK == /\ slot \in [Keys -> Reqs \cup {None}]
          /\ last \in Keys \X (Reqs \cup {None})
Init == slot = [k \in Keys |-> None] /\ last = <<CHOOSE k \in Keys : TRUE, None>>
Next == \/ \E k \in Keys, r \in Reqs : /\ slot[k] = None
                                      /\ r.key = k
                                      /\ slot' = [slot EXCEPT ![k] = r]
                                      /\ last' = <<k, r>>
        \/ \E k \in Keys : /\ slot[k] /= None
                           /\ slot[k].kind = "put"
                           /\ slot' = [slot EXCEPT ![k] = None]
                           /\ last' = <<k, None>>
GetsStay == \A k \in Keys : slot[k] = None \/ slot[k].kind = "put"
====
