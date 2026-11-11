---- MODULE MixedStr ----
\* A variable that holds an integer or a string: held and printed freely, compared only where TLC
\* can compare (here against values of its current kind and model values)
EXTENDS Naturals
CONSTANTS None
VARIABLES x, isNum
Init == x = "idle" /\ isNum = FALSE
Next == \/ /\ ~isNum
           /\ x' = IF x = "idle" THEN 1 ELSE 2
           /\ isNum' = TRUE
        \/ /\ isNum
           /\ x' = IF x = 1 THEN "busy" ELSE "idle"
           /\ isNum' = FALSE
Inv == /\ x # None
       /\ isNum \/ x \in {"idle", "busy"}
       /\ ~isNum \/ x \in {1, 2}
\* Violated: the counterexample prints a string and an integer in one variable
NotBusy == isNum \/ x # "busy"
====
