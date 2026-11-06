---- MODULE Records ----
EXTENDS Naturals, FiniteSets
CONSTANTS Procs
VARIABLE r, msgs, f
Msg == [src : Procs, val : 0..2]
TypeOK == /\ r \in [a : 0..2, b : {"on", "off"}]
          /\ msgs \subseteq Msg
          /\ f \in [Procs -> [cnt : 0..2, flag : BOOLEAN]]
Init == /\ r = [a |-> 0, b |-> "off"]
        /\ msgs = {}
        /\ f = [p \in Procs |-> [cnt |-> 0, flag |-> FALSE]]
Send(p) == /\ f[p].cnt < 2
           /\ msgs' = msgs \cup {[src |-> p, val |-> f[p].cnt]}
           /\ f' = [f EXCEPT ![p].cnt = @ + 1, ![p].flag = ~@]
           /\ r' = [r EXCEPT !.a = Cardinality(msgs') % 3]
Recv == \E m \in msgs :
          /\ m.val > 0
          /\ msgs' = msgs \ {m}
          /\ r' = [r EXCEPT !.b = IF @ = "on" THEN "off" ELSE "on", !.a = m.val]
          /\ UNCHANGED f
Flip == /\ \E S \in SUBSET Procs :
             /\ Cardinality(S) = 1
             /\ f' = [p \in Procs |-> IF p \in S THEN [f[p] EXCEPT !.flag = TRUE] ELSE f[p]]
        /\ UNCHANGED <<r, msgs>>
Next == (\E p \in Procs : Send(p)) \/ Recv \/ Flip
Inv == /\ {m.src : m \in msgs} \subseteq Procs
       /\ \A m \in msgs : m.val <= 2
       /\ Cardinality({m \in msgs : m.val = 2}) <= 2
       /\ r.a # 2 \/ r.b = "off" \/ \E p \in Procs : f[p].flag
====
