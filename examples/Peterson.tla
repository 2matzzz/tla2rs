---------------------------- MODULE Peterson ----------------------------
(* Peterson's mutual exclusion for processes 0 and 1. *)
EXTENDS Naturals

VARIABLES flag, turn, pc

Procs == {0, 1}
Other(p) == 1 - p

TypeOK == /\ flag \in [Procs -> BOOLEAN]
          /\ turn \in Procs
          /\ pc \in [Procs -> {"idle", "setFlag", "setTurn", "wait", "cs"}]

Init == /\ flag = [p \in Procs |-> FALSE]
        /\ turn = 0
        /\ pc = [p \in Procs |-> "idle"]

Go(p, from, to) == pc[p] = from /\ pc' = [pc EXCEPT ![p] = to]

Start(p) == Go(p, "idle", "setFlag") /\ UNCHANGED <<flag, turn>>
SetFlag(p) == Go(p, "setFlag", "setTurn") /\ flag' = [flag EXCEPT ![p] = TRUE] /\ UNCHANGED turn
SetTurn(p) == Go(p, "setTurn", "wait") /\ turn' = Other(p) /\ UNCHANGED flag
Enter(p) == /\ Go(p, "wait", "cs")
            /\ ~flag[Other(p)] \/ turn = p
            /\ UNCHANGED <<flag, turn>>
Exit(p) == Go(p, "cs", "idle") /\ flag' = [flag EXCEPT ![p] = FALSE] /\ UNCHANGED turn

ProcNext(p) == Start(p) \/ SetFlag(p) \/ SetTurn(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : ProcNext(p)

vars == <<flag, turn, pc>>

\* Weak fairness for each process. A waiting process eventually enters (no starvation)
Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(ProcNext(p))

NoStarvation == \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")
\* A process can't stay idle forever (Start is also fair), so 0 enters infinitely often
InfOftenCS == []<>(pc[0] = "cs")

\* Fairness for process 0 only. Process 1 can get stuck in wait, so NoStarvation is violated
SpecOnly0 == Init /\ [][Next]_vars /\ WF_vars(ProcNext(0))

MutualExclusion == ~(pc[0] = "cs" /\ pc[1] = "cs")
=============================================================================
