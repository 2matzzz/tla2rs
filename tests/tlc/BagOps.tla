---- MODULE BagOps ----
\* IsABag, DOMAIN of a record, STRING and Nat as supersets in constants, and BagOfAll with an
\* operator whose body is a literal (TLC passes it as that value and stops with an error)
EXTENDS Integers, Bags, FiniteSets
CONSTANT Idle
ASSUME /\ IsABag(<<1, 2>>) /\ ~IsABag(<<0>>) /\ ~IsABag({}) /\ IsABag([a |-> 2]) /\ IsABag(EmptyBag)
       /\ DOMAIN [a |-> 1, b |-> 2] = {"a", "b"}
       /\ {1, 2} \subseteq Nat /\ ~({-1} \subseteq Nat) /\ {"a"} \subseteq STRING
       /\ ~IsFiniteSet(Nat) /\ Idle \notin STRING
VARIABLES items, n
TypeOK == n \in 0..3
Init == items = EmptyBag /\ n = 0
Next == \/ /\ n < 3
           /\ n' = n + 1
           /\ items' = items (+) SetToBag({n'})
        \/ UNCHANGED <<items, n>>
Inv == /\ IsABag(items)
       /\ IsABag(<<n>>) = (n > 0)
       /\ ~IsABag(<<n, "a">>)
       /\ BagOfAll(LAMBDA y : y + 1, items) = BagOfAll(LAMBDA y : 1 + y, items)
\* Fails once items holds 2: the operator below is the literal 0 to TLC
Lit == n < 2 \/ BagOfAll(LAMBDA y : 0, items) # EmptyBag
====
