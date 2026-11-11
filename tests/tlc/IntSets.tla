---- MODULE IntSets ----
\* Integer ranges with bounds from the state as values, products of sets from the state as values,
\* subsets of Nat and Int, and SUBSET of a set in the state as a type test
EXTENDS Integers, FiniteSets
VARIABLES x, S
Init == x = -2 /\ S = {}
Next == /\ x' = (IF x < 2 THEN x + 1 ELSE -2)
        /\ S' = IF x > 0 THEN S \cup {x} ELSE S
Inv == /\ S \subseteq Nat /\ {x} \subseteq Int /\ S \in SUBSET Nat
       /\ Cardinality(x..2) = 2 - x + 1 /\ x..(x - 1) = {}
       /\ IsFiniteSet(x..2) /\ (x..2) \cap (0..1) \subseteq 0..1
       /\ Cardinality(S \X S) = Cardinality(S) * Cardinality(S)
       /\ {y \in -2..x : y < 0} \subseteq Int
       /\ x \geq -2 /\ x \leq 2 /\ x =< 2
\* Violated
Small == Cardinality(S \X (x..2)) < 3
====
