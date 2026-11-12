---- MODULE EnSubst ----
\* While TLC computes whether an action is enabled for an ENABLED or a WF written in an
\* instantiated module, a substituted variable is bound by its name, as if it were a variable of its
\* own, and its substitution is not read primed: Bump can never take a step here, yet TLC finds it
\* enabled. An ENABLED written here reads the substitution (Outer)
EXTENDS Naturals
VARIABLE p, q, k
Init == p = 0 /\ q = 0 /\ k = 0
Next == k' = 1 - k /\ UNCHANGED <<p, q>>
Spec == Init /\ [][Next]_<<p, q, k>> /\ WF_k(Next)
I == INSTANCE EnSubstInner WITH sum <- p + q
WKeep == I!WKeep
WBump == I!WBump
ENone == I!ENone
EPick == I!EPick
ETwice == I!ETwice
EReread == I!EReread
ESame == I!ESame
EEarly == I!EEarly
Outer == []<>ENABLED I!Pick
====
