---------------------------- MODULE PcalSumProc ----------------------------
\* Processes, with, and a label inside an if
EXTENDS Naturals

(* --algorithm Procs
variables t = 0;
fair process w \in 1..2
variables k = 0;
begin
P:
  while k < 2 do
    with d \in {1, 2} do
      t := (t + d) % 3;
    end with;
    if t = 0 then
Q:
      k := k + 1;
    else
      k := k + 2;
    end if;
  end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7a0ab74f" /\ chksum(tla) = "e6aff37a")
VARIABLES t, pc, k

vars == << t, pc, k >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ t = 0
        (* Process w *)
        /\ k = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF k[self] < 2
                 THEN /\ \E d \in {1, 2}:
                           t' = (t + d) % 3
                      /\ IF t' = 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "Q"]
                                 /\ k' = k
                            ELSE /\ k' = [k EXCEPT ![self] = k[self] + 2]
                                 /\ pc' = [pc EXCEPT ![self] = "P"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << t, k >>

Q(self) == /\ pc[self] = "Q"
           /\ k' = [k EXCEPT ![self] = k[self] + 1]
           /\ pc' = [pc EXCEPT ![self] = "P"]
           /\ t' = t

w(self) == P(self) \/ Q(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: w(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..2 : WF_vars(w(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
