---- MODULE LazyFun ----
\* Functions over sets that cannot be enumerated (Nat, Int, STRING, Seq(S), a product with one of
\* them) or that have more than 65536 elements: TLC evaluates them only where they are applied,
\* and so does tla2rs (application, also after EXCEPT, and membership in their DOMAIN)
EXTENDS Integers, TLC, Sequences
VARIABLES x, s
Double == [n \in Nat |-> 2 * n]
Square == [n \in Int |-> n * n]
Suffix == [t \in STRING |-> t \o "x"]
Length == [q \in Seq({1, 2}) |-> Len(q)]
Pair == [a \in Nat, c \in Nat |-> a * 10 + c]
Mod7 == [i \in 0..200000 |-> i % 7]
Init == x = 0 /\ s \in {"a", "bc"}
Next == /\ x < 30
        /\ x' = Double[x] + Len(Suffix[s]) + Mod7[x * 1000] + Length[<<1, 2, 1>>]
        /\ UNCHANGED s
Inv == /\ Square[-x] = x * x
       /\ x \in DOMAIN Double
       /\ -1 \notin DOMAIN Double
       /\ [Double EXCEPT ![x] = 5, ![-1] = 6][x] = 5
       /\ [Double EXCEPT ![x] = @ + 1, ![x + 1] = @ * 3][x + 1] = 6 * (x + 1)
       /\ [n \in Nat |-> n + x][3] = 3 + x
       /\ Pair[x, 3] = x * 10 + 3
       /\ Pair[<<0, x>>] = x
\* Evaluation errors: an argument outside the domain, also where EXCEPT names it
Below == Double[x - 1] >= 0
ExceptBelow == [Double EXCEPT ![-1] = 7][-1] = 7
NextBelow == x < 3 /\ x' = Double[x - 1] /\ UNCHANGED s
====
