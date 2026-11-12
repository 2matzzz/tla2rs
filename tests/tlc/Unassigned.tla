---- MODULE Unassigned ----
\* An action that leaves variables unassigned: an \A over an empty set swallows the assignments in
\* its body. TLC reports the action (by name when the next-state relation has more than one), the
\* variables in the order of their names, counts the successor and shows it with them null
EXTENDS Naturals
VARIABLES s, t, b
TypeOK == s \in SUBSET {1, 2} /\ t \in 0..9 /\ b \in 0..9
Init == s = {} /\ t = 0 /\ b = 0
InitPart == t = 0 /\ b = 0 /\ \A r \in {} : s = {r}
Drain == \A r \in s : s' = s \ {r} /\ t' = t /\ b' = b
Step == t < 2 /\ t' = t + 1 /\ UNCHANGED <<s, b>>
Late == t = 2 /\ b' = 1 /\ \A r \in s : s' = s \ {r} /\ t' = r
Pick == \E k \in {1, 2} : \A r \in s : s' = s \ {r, k} /\ t' = k /\ b' = k
Next == Drain
NextNamed == Step \/ Late
Eventually == <>(t = 5)
====
