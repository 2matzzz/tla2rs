---- MODULE ViewSymSet ----
(* VIEW and SYMMETRY with a set of records in the view. `pad` widens the record type past 128
   values, so msgs is stored as a sorted array and permuting it reorders the elements. *)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, MaxN

VARIABLES msgs, cnt

Msg == [from : Nodes, to : Nodes, n : 0..MaxN, pad : 0..15]

TypeOK == /\ msgs \subseteq Msg
          /\ Cardinality(msgs) <= 3
          /\ cnt \in [Nodes -> 0..MaxN]

Init == msgs = {} /\ cnt = [x \in Nodes |-> 0]

Send(a, b) == /\ a # b
              /\ cnt[a] < MaxN
              /\ Cardinality(msgs) < 3
              /\ msgs' = msgs \cup {[from |-> a, to |-> b, n |-> cnt[a], pad |-> 0]}
              /\ cnt' = [cnt EXCEPT ![a] = @ + 1]

Recv(m) == /\ msgs' = msgs \ {m}
           /\ cnt' = [cnt EXCEPT ![m.to] = IF @ > 0 THEN @ - 1 ELSE 0]

Next == (\E a, b \in Nodes : Send(a, b)) \/ (\E m \in msgs : Recv(m))

View == <<cnt, msgs>>
Symmetry == Permutations(Nodes)
====
