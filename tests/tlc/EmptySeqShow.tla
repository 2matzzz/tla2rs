---- MODULE EmptySeqShow ----
\* TLC prints an empty tuple as <<>> (from <<>>, Tail, SubSeq, \o or SelectSeq) and an empty function
\* built by [k \in S |-> e] over an empty S as << >>, when it starts and while it explores. The
\* invariant compares ToString with the text TLC makes for each
EXTENDS Naturals, Sequences, TLC
VARIABLES d, q, r, n
ASSUME PrintT(<<<<>>, Tail(<<1>>), SubSeq(<<1, 2>>, 2, 1), <<>> \o <<>>, SelectSeq(<<1>>, LAMBDA x : FALSE),
                [k \in {} |-> 1], [k \in 1..0 |-> 1], [i \in 1..2 |-> <<>>], {<<>>, [k \in {} |-> 1]},
                {[k \in {} |-> 1], <<>>}, Tail(<<1>>) \o <<>>, <<[k \in {} |-> 0]>>>>)
ASSUME ToString([k \in {} |-> 1]) = "<< >>" /\ ToString(Tail(<<1>>)) = "<<>>"
Init == /\ d = [k \in {} |-> 0]
        /\ q = <<1>>
        /\ r = <<>>
        /\ n = 0
Next == \/ /\ n < 3 /\ n' = n + 1
           /\ d' = IF n = 0 THEN <<>> ELSE [k \in 1..(n - 1) |-> 0]
           /\ q' = IF n = 0 THEN Tail(q) ELSE SelectSeq(<<1, 2>>, LAMBDA x : x > n)
           /\ r' = IF n = 1 THEN Append(r, 2) ELSE r
           /\ PrintT(<<n, d, q, r, ToString(d), ToString(q), ToString(<<d>>)>>)
        \/ n = 3 /\ UNCHANGED <<d, q, r, n>>
Inv == /\ ToString(d) = <<"<< >>", "<<>>", "<< >>", "<<0>>">>[n + 1]
       /\ ToString(q) = <<"<<1>>", "<<>>", "<<2>>", "<<>>">>[n + 1]
====
