---- MODULE CmBag ----
\* BagsExt (CommunityModules) on a bag from the state; a fold that is not commutative shows the
\* order the elements and their copies are taken in
EXTENDS Naturals, Sequences, Bags, BagsExt, TLC
VARIABLES b, r
Facts(B) == <<BagRemove(B, 1), BagRemoveAll(B, 2), SumBag(B), ProductBag(B), FoldBag(LAMBDA x, y : 10 * x + y, 0, B),
              MapThenFoldBag(LAMBDA x, y : x \o y, <<>>, LAMBDA x : <<x + 5>>, LAMBDA T : CHOOSE x \in T : TRUE, B)>>
Init == b = EmptyBag /\ r = Facts(EmptyBag)
Next == \E x \in {1, 2, 3} : BagCardinality(b) < 4 /\ b' = BagAdd(b, x) /\ r' = Facts(b')
ASSUME PrintT(<<BagAdd(SetToBag({1}), 1), BagRemove(SetToBag({1}), 2), SumBag(EmptyBag)>>)
====
