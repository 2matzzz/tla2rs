---- MODULE SparseBag ----
\* Bags whose elements have a large or unbounded type, held as their sorted (element, count)
\* pairs: (+), (-), \sqsubseteq, SetToBag, BagToSet, CopiesIn, application, BagCardinality,
\* BagUnion, BagOfAll, SubBag, and a bag in [D -> R]
EXTENDS Integers, TLC, Bags, FiniteSets
VARIABLES x, b, m
Init == x = 0 /\ b = EmptyBag /\ m = EmptyBag
Next == \/ /\ x < 4
           /\ x' = x + 1
           /\ b' = b (+) SetToBag({x * 100000})
           /\ m' = m (+) SetToBag({[src |-> x % 2, val |-> x * 1000000]})
        \/ /\ \E e \in BagToSet(b) : b' = b (-) SetToBag({e})
           /\ UNCHANGED <<x, m>>
        \/ /\ x < 4
           /\ x' = x + 1
           /\ b' = b (+) SetToBag({0})
           /\ UNCHANGED m
Inv == /\ BagCardinality(b) <= x
       /\ \A e \in BagToSet(b) : CopiesIn(e, b) >= 1 /\ b[e] = CopiesIn(e, b)
       /\ CopiesIn(12345, b) = 0
       /\ IsABag(b) /\ b \sqsubseteq b (+) b
       /\ ~(b (+) b \sqsubseteq b) \/ b = EmptyBag
       /\ BagUnion({b, b (+) b}) = b (+) b (+) b
       /\ BagCardinality(m) <= x
       /\ \A r \in BagToSet(m) : r.val \in {i * 1000000 : i \in 0..3}
       /\ BagCardinality(BagOfAll(LAMBDA r : r.val, m)) = BagCardinality(m)
       /\ BagCardinality(b) <= 2 =>
            Cardinality(SubBag(b)) = IF Cardinality(BagToSet(b)) = 2 THEN 4 ELSE BagCardinality(b) + 1
       /\ b \in [BagToSet(b) -> 1..4]
\* Violated: the counterexample prints these bags
Few == BagCardinality(b) < 3 \/ CopiesIn(0, b) < 2
====
