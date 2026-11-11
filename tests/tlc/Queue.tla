---- MODULE Queue ----
\* Sequences in the state: a bounded queue, with Append / Head / Tail / SubSeq / \o / SelectSeq
EXTENDS Naturals, Sequences
CONSTANTS Items, Cap
VARIABLES q, out
TypeOK == q \in Seq(Items) /\ out \in Seq(Items)
Init == q = <<>> /\ out = <<>>
Send(i) == /\ Len(q) < Cap
           /\ q' = Append(q, i)
           /\ UNCHANGED out
Recv == /\ q # <<>>
        /\ out' = IF Len(out) < Cap THEN out \o <<Head(q)>> ELSE <<Head(q)>>
        /\ q' = Tail(q)
Drop == /\ Len(q) >= 2
        /\ q' = SubSeq(q, 2, Len(q))
        /\ UNCHANGED out
Keep(i) == /\ q' = SelectSeq(q, LAMBDA x : x # i)
           /\ q' # q
           /\ UNCHANGED out
Next == (\E i \in Items : Send(i) \/ Keep(i)) \/ Recv \/ Drop
Inv == /\ Len(q) <= Cap
       /\ \A k \in DOMAIN q : q[k] \in Items
       /\ q = [k \in 1..Len(q) |-> q[k]]
       /\ out \in Seq(Items)
\* Violated: the counterexample prints sequences
Never == ~(Len(q) = Cap /\ Len(out) = 2)
Bound == Len(q) <= Cap /\ Len(out) <= Cap
====
