---- MODULE PartExcept ----
\* x' = [x EXCEPT ![k] = e] on a function over part of a type (model values and two integers):
\* updated in place
EXTENDS Naturals
CONSTANT Workers
VARIABLE at
Ids == Workers \cup {0} \cup {10}
Init == at = [i \in Ids |-> "idle"]
Next == \/ \E w \in Workers : at[w] = "idle" /\ at' = [at EXCEPT ![w] = "busy"]
        \/ at[0] = "idle" /\ \A w \in Workers : at[w] = "busy" /\ at' = [at EXCEPT ![0] = "busy"]
        \/ at[10] = "idle" /\ at[0] = "busy" /\ at' = [at EXCEPT ![10] = "busy"]
AllBusy == \E i \in Ids : at[i] = "idle"
====
