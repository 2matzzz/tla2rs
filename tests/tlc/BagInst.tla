---- MODULE BagInst ----
\* Named instances of Bags and Sequences, with operators passed to BagOfAll and SelectSeq; bags
\* of records with different fields
EXTENDS Naturals, Bags
B == INSTANCE Bags
S == INSTANCE Sequences
VARIABLE b, r
Init == b = SetToBag({1, 2}) /\ r = SetToBag({[a |-> 1], [a |-> 2, c |-> TRUE]})
Next == \/ b' = b (+) SetToBag({1}) /\ UNCHANGED r
        \/ r' = r (+) SetToBag({[a |-> 1]}) /\ UNCHANGED b
Con == BagCardinality(b) < 4 /\ BagCardinality(r) < 4
Double(n) == 2 * n
Inv == /\ B!BagOfAll(Double, b) = BagOfAll(Double, b)
       /\ B!CopiesIn(2, B!BagOfAll(Double, b)) = CopiesIn(1, b)
       /\ S!SelectSeq(<<1, 2, 3>>, LAMBDA i : i > 1) = <<2, 3>>
       /\ IsABag(r) /\ B!IsABag(r)
       /\ BagToSet(r) \subseteq {[a |-> 1], [a |-> 2, c |-> TRUE]}
       /\ BagCardinality(r) >= 2
Twice == CopiesIn([a |-> 1], r) < 2
====
