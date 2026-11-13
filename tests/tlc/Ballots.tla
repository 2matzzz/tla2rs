---- MODULE Ballots ----
\* Messages of two kinds, records of different fields. The field one kind lacks holds a function
\* over records with a ballot that grows without a bound in the spec: compared with the tuples of
\* the set of messages, and packed while absent
EXTENDS Naturals
Votes == [1..2 -> [bal : 0..3, val : {"x", "y"}]]
Msgs == [type : {"prepare"}, bal : 0..3] \cup [type : {"vote"}, bal : 0..3, votes : Votes]
VARIABLES msgs, b
Init == msgs = {} /\ b = 0
Next == /\ b' = b + 1
        /\ \/ msgs' = msgs \cup {[type |-> "prepare", bal |-> b]}
           \/ \E v \in {"x", "y"} :
                msgs' = msgs \cup {[type |-> "vote", bal |-> b, votes |-> [i \in 1..2 |-> [bal |-> b, val |-> v]]]}
Bound == b <= 2
Valid == \A m \in msgs : m \in Msgs
====
