---- MODULE SubBags ----
\* SubBag of a bag held in the state, iterated in TLC's order (CHOOSE picks what TLC picks)
EXTENDS Integers, Bags, FiniteSets
VARIABLES b, pick
Init == b = SetToBag({1}) /\ pick = EmptyBag
Next == \/ /\ BagCardinality(b) < 4
           /\ \E e \in {1, 2, 3} : b' = b (+) SetToBag({e})
           /\ pick' = IF \E s \in SubBag(b') : BagCardinality(s) = 2 /\ s # pick
                      THEN CHOOSE s \in SubBag(b') : BagCardinality(s) = 2 /\ s # pick
                      ELSE pick
        \/ /\ b # SetToBag({1})
           /\ b' = SetToBag({1})
           /\ UNCHANGED pick
Inv == /\ \A s \in SubBag(b) : s \sqsubseteq b
       /\ Cardinality(SubBag(b)) >= 2
\* Violated
NotTwos == pick # SetToBag({2}) (+) SetToBag({2})
====
