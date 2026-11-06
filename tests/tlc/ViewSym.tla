---------------------------- MODULE ViewSym ----------------------------
(* Uses VIEW and SYMMETRY together. Time advances without bound; the VIEW keeps only offsets
   from now. Nodes are interchangeable. *)
EXTENDS Integers, TLC

CONSTANTS Nodes, Horizon, MaxTime

VARIABLES now, mark, phase

TypeOK == /\ now \in 0..MaxTime
          /\ mark \in [Nodes -> Int]
          /\ phase \in [Nodes -> {"idle", "run"}]

Init == /\ now = 0
        /\ mark = [n \in Nodes |-> 0]
        /\ phase = [n \in Nodes |-> "idle"]

Start(n) == /\ phase[n] = "idle"
            /\ phase' = [phase EXCEPT ![n] = "run"]
            /\ mark' = [mark EXCEPT ![n] = now]
            /\ now' = now

Stop(n) == /\ phase[n] = "run"
           /\ now - mark[n] >= 2
           /\ phase' = [phase EXCEPT ![n] = "idle"]
           /\ UNCHANGED <<now, mark>>

Tick == now < MaxTime /\ now' = now + 1 /\ UNCHANGED <<mark, phase>>

Next == (\E n \in Nodes : Start(n) \/ Stop(n)) \/ Tick

Spec == Init /\ [][Next]_<<now, mark, phase>>

\* mark never runs ahead of now while a node is running
MarkSane == \A n \in Nodes : mark[n] <= now

Rel(t) == IF t - now < -Horizon THEN -Horizon ELSE t - now
View == << [n \in Nodes |-> Rel(mark[n])], phase >>
Symmetry == Permutations(Nodes)
=============================================================================
