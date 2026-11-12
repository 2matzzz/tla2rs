---- MODULE StrRankNum ----
\* TLC creates a string for each number token as written, with the identifiers of each module
\* (`1` and `0` in Sequences), so these strings come before the other string literals
EXTENDS Sequences
VARIABLES x, y
Init == /\ x = {"zz", "9", "2", "1", "0", "007", "x"}
        /\ y = CHOOSE e \in x : e # "x"
Next == UNCHANGED <<x, y>>
Inv == x = {} \/ 007 = 9
====
