---- MODULE BagMsgs ----
\* A bag of messages in the state (Bags module): (+), (-), CopiesIn, BagIn, BagToSet,
\* BagCardinality, \sqsubseteq, BagOfAll, BagUnion, and printing a bag as a function
EXTENDS Integers, Bags
CONSTANTS Msgs
VARIABLES net, got
Init == net = EmptyBag /\ got = EmptyBag
Send(m) == /\ CopiesIn(m, net) < 2
           /\ net' = net (+) SetToBag({m})
           /\ UNCHANGED got
Recv(m) == /\ BagIn(m, net)
           /\ net' = net (-) SetToBag({m})
           /\ got' = got (+) SetToBag({m})
Next == \E m \in Msgs : Send(m) \/ (BagCardinality(got) < 2 /\ Recv(m))
Inv == /\ BagToSet(net) \subseteq Msgs
       /\ \A m \in BagToSet(net) : net[m] = CopiesIn(m, net)
       /\ SetToBag(BagToSet(got)) \sqsubseteq got \/ got = EmptyBag
       /\ BagCardinality(BagOfAll(LAMBDA m : m % 2, net)) = BagCardinality(net)
       /\ DOMAIN got = BagToSet(got)
\* Violated (the union of a set holding net once, when got = net)
UnionOk == BagUnion({net, got}) = net (+) got
\* Violated: the counterexample prints bags
Few == BagCardinality(net) + BagCardinality(got) < 3
====
