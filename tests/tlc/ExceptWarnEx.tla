---- MODULE ExceptWarnEx ----
\* An EXCEPT warning raised in a branch of an action: TLC checks each successor as it computes it,
\* so the warning of a later branch comes after the error on an earlier one (and again while TLC
\* rebuilds the behavior)
EXTENDS Naturals
VARIABLES t, r, n
Init == t = <<0, 0>> /\ r = [a |-> 0] /\ n = 0
Next == /\ n < 2
        /\ n' = n + 1
        /\ \E k \in {1, 3} : t' = [t EXCEPT ![k] = @ + n']
        /\ r' = r
NextRec == /\ n < 2
           /\ n' = n + 1
           /\ t' = t
           /\ \/ r' = [r EXCEPT !.a = @ + n']
              \/ r' = [r EXCEPT !.z = n']
NextTwo == /\ n < 2
           /\ n' = n + 1
           /\ \/ t' = [t EXCEPT ![3] = n'] /\ r' = r
              \/ r' = [r EXCEPT !.z = n'] /\ t' = t
Inv == t[1] = 0
InvRec == r.a = 0
InvPass == n < 5
====
