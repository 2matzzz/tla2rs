------------------------------ MODULE PcalSumC ------------------------------
\* The C-syntax
EXTENDS Naturals

(* --algorithm Cee {
  variables a = 0;
  process (u \in {1, 2})
    variables b = 0;
  {
  L1: while (b < 2) {
        if (a < 3) { a := a + 1 } else { a := 0 };
        b := b + 1;
      }
  }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "6d558977" /\ chksum(tla) = "a163d78")
VARIABLES a, pc, b

vars == << a, pc, b >>

ProcSet == ({1, 2})

Init == (* Global variables *)
        /\ a = 0
        (* Process u *)
        /\ b = [self \in {1, 2} |-> 0]
        /\ pc = [self \in ProcSet |-> "L1"]

L1(self) == /\ pc[self] = "L1"
            /\ IF b[self] < 2
                  THEN /\ IF a < 3
                             THEN /\ a' = a + 1
                             ELSE /\ a' = 0
                       /\ b' = [b EXCEPT ![self] = b[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "L1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << a, b >>

u(self) == L1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2}: u(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
