---- MODULE Inst ----
\* A named instance and a parameterized one, with WITH substitutions. As in TLC, the ASSUME of the
\* instantiated module is not checked, and its LOCAL definitions are not visible
EXTENDS Naturals
VARIABLE a, b
A == INSTANCE Counter WITH Limit <- 2, c <- a
B(n) == INSTANCE Counter WITH Limit <- n, c <- b
Zero == INSTANCE Counter WITH Limit <- 0, c <- a
Init == A!Init /\ B(3)!Init
Next == \/ A!Next /\ UNCHANGED b
        \/ B(3)!Next /\ UNCHANGED a
Inv == A!TypeOK /\ B(3)!TypeOK /\ A!Total(2) /\ ~(a = 2 /\ b = 3)
====
