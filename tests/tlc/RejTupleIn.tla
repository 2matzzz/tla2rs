---- MODULE RejTupleIn ----
\* TLC stops with an error when it compares a tuple with the elements of a set of integers held
\* in the state (but not when the set is empty)
EXTENDS Naturals
VARIABLE s, t
TypeOK == s \subseteq 1..3 /\ t \in {1, 2} \X {3}
Init == s = {} /\ t = <<1, 3>>
Next == /\ s' = IF s = {} THEN {2} ELSE s
        /\ t \notin s
        /\ UNCHANGED t
====
