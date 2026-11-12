---- MODULE FpErr ----
\* TLC reports a second error after the behavior, `TLC was unable to fingerprint.`, when the error
\* is raised inside a value it built from an expression written there (a set, a tuple, ...), and
\* not when the value comes from the state or is an interval
EXTENDS Naturals
VARIABLES x, n, s, t
Init == x = "idle" /\ n = 0 /\ s = {5, 6} /\ t = <<5, 6>>
NextInSet ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ x \in {5, 6}
NextInCup ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ x \in {5} \cup {6}
NextNotIn ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ x \notin {5, 6}
NextInRange ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ x \in 5..6
NextExists ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ \E y \in {5, 6} : y = x
NextTupApp ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ <<5, 6, 7>>[n + 4] > 0
NextVarApp ==
        /\ n' = (n + 1) % 3
        /\ UNCHANGED <<x, s, t>>
        /\ t[n + 4] > 0
NextRangeMix ==
        /\ n' = (n + 1) % 3
        /\ x' = IF n = 1 THEN 5 ELSE "idle"
        /\ UNCHANGED <<s, t>>
        /\ n = 0 \/ x \in 5..6
====
