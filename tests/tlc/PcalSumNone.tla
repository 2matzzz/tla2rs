------------------------------ MODULE PcalSumNone ------------------------------
\* No checksums in the translation line: nothing is checked
EXTENDS Naturals

(* --algorithm Sum
variables x = 0, y = 0;
begin
A:
  while x < 2 do
    either
      x := x + 1;
    or
      y := y + 1;
    end either;
B:
    if y > 1 then
      y := 0;
    else
C:
      y := y + x + 0;
    end if;
  end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = "A"

A == /\ pc = "A"
     /\ IF x < 2
           THEN /\ \/ /\ x' = x + 1
                      /\ y' = y
                   \/ /\ y' = y + 1
                      /\ x' = x
                /\ pc' = "B"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << x, y >>

B == /\ pc = "B"
     /\ IF y > 1
           THEN /\ y' = 0
                /\ pc' = "A"
           ELSE /\ pc' = "C"
                /\ y' = y
     /\ x' = x

C == /\ pc = "C"
     /\ y' = y + x
     /\ pc' = "A"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == A \/ B \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
