---- MODULE LazyAction ----
\* Where TLC computes the successors of an action (while some variable is unassigned), it evaluates a
\* LET definition or an argument again at each use; once every variable is assigned, and inside an
\* expression, it keeps the value
EXTENDS Naturals, TLC
VARIABLES x, y
Both(a) == a /\ a
Init == /\ Both(PrintT(<<"init-open", 0>>))
        /\ x = 0
        /\ LET d == PrintT(<<"init-one-left", x>>) IN d /\ d
        /\ y = 0
        /\ LET d == PrintT(<<"init-done", x>>) IN d /\ d
Next == /\ x < 2
        /\ LET d == PrintT(<<"let", x>>) IN d /\ d
        /\ Both(PrintT(<<"arg", x>>))
        /\ LET d == PrintT(<<"cond", x>>) IN IF d THEN d ELSE FALSE
        /\ LET d == PrintT(<<"exists", x>>) IN \E i \in 1..2 : d
        /\ Both(PrintT(<<"in-expr", x>>)) = TRUE
        /\ x' = x + 1
        /\ LET d == PrintT(<<"one-left", x>>) IN d /\ d
        /\ y' = y
        /\ LET d == PrintT(<<"done", x>>) IN d /\ d
        /\ Both(PrintT(<<"done-arg", x>>))
Inv == TRUE
====
