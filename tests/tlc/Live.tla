---- MODULE Live ----
EXTENDS Naturals
CONSTANTS P
VARIABLE pc, lock
vars == <<pc, lock>>
TypeOK == /\ pc \in [P -> {"idle", "wait", "cs"}]
          /\ lock \in BOOLEAN
Init == pc = [p \in P |-> "idle"] /\ lock = FALSE
Try(p) == pc[p] = "idle" /\ pc' = [pc EXCEPT ![p] = "wait"] /\ UNCHANGED lock
Enter(p) == pc[p] = "wait" /\ ~lock /\ lock' = TRUE /\ pc' = [pc EXCEPT ![p] = "cs"]
Exit(p) == pc[p] = "cs" /\ lock' = FALSE /\ pc' = [pc EXCEPT ![p] = "idle"]
Spin(p) == pc[p] = "wait" /\ lock /\ UNCHANGED vars
Next == \E p \in P : Try(p) \/ Enter(p) \/ Exit(p) \/ Spin(p)
SpecWeak == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
SpecSpin == Init /\ [][Next]_vars /\ \A p \in P : WF_vars(Spin(p)) /\ WF_vars(Exit(p))
SpecNext == Init /\ [][Next]_vars /\ WF_vars(Next)
Starve == \A p \in P : (pc[p] = "wait") ~> (pc[p] = "cs")
SomeCS == []<>(\E p \in P : pc[p] = "cs")
EvIdle == <>[](\A p \in P : pc[p] = "idle")
====
