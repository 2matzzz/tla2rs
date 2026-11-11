---- MODULE StrState ----
\* Strings built from the state: ToString of state values, SubSeq of a string, and STRING
EXTENDS Integers, Sequences, TLC
CONSTANT Idle
VARIABLES name, n, flag, log
Names == {"alpha", "beta"}
Init == /\ name \in Names
        /\ n \in -1..1
        /\ flag = FALSE
        /\ log = ToString(<<name, n, flag>>)
Next == \/ /\ n < 3
           /\ n' = n + 1
           /\ UNCHANGED <<name, flag>>
           /\ log' = ToString(n') \o ":" \o SubSeq(name, 1, n' + 1)
        \/ /\ flag' = ~flag
           /\ UNCHANGED <<name, n>>
           /\ log' = IF flag' THEN ToString(<<Idle, flag'>>) ELSE SubSeq(name, 2, 1)
TypeOK == /\ n \in -1..3 /\ flag \in BOOLEAN /\ log \in STRING /\ Idle \notin STRING /\ name \in STRING
          /\ {log, name} \subseteq STRING
Inv == /\ Len(log) <= 22
       /\ log # "4:alpha"
       /\ ToString(n) = IF n < 0 THEN "-1" ELSE SubSeq("0123", n + 1, n + 1)
       /\ ToString(flag) \in {"TRUE", "FALSE"}
\* Violated
Short == log # "<<Idle, TRUE>>"
====
