---- MODULE SetAtom ----
\* A function holding model values and sets of model values, typed by inference (no type
\* invariant): applied, iterated, compared with {} and collected in a set
EXTENDS FiniteSets
CONSTANT Procs, Unset
VARIABLE hold, flag, at, seen
Init == /\ hold = [p \in Procs |-> Unset]
        /\ flag = [p \in Procs |-> FALSE]
        /\ at = [p \in Procs |-> "a"]
        /\ seen = {Unset}
Pick(p) == /\ at[p] = "a"
           /\ \E q \in Procs : hold' = [hold EXCEPT ![p] = q]
           /\ at' = [at EXCEPT ![p] = "b"]
           /\ UNCHANGED flag
Look(p) == /\ at[p] = "b"
           /\ flag' = [flag EXCEPT ![p] = ~flag[hold[p]]]
           /\ hold' = [hold EXCEPT ![p] = Procs \ {p}]
           /\ at' = [at EXCEPT ![p] = "c"]
Drop(p) == /\ at[p] = "c"
           /\ IF hold[p] # {}
                 THEN /\ \E q \in hold[p] : hold' = [hold EXCEPT ![p] = hold[p] \ {q}]
                      /\ at' = at
                 ELSE /\ hold' = [hold EXCEPT ![p] = Unset]
                      /\ at' = [at EXCEPT ![p] = "a"]
           /\ UNCHANGED flag
Next == \E p \in Procs : /\ Pick(p) \/ Look(p) \/ Drop(p)
                         /\ seen' = seen \cup {hold'[p]}
NeverEmpty == \A p \in Procs : hold[p] /= {}
====
