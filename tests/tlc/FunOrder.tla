---- MODULE FunOrder ----
EXTENDS Integers, Bags, TLC
\* TLC compares functions by the size of their domain, then key and value pair by pair; functions
\* over different parts of a type, and (d :> e) @@ f with d outside the domain of f
VARIABLE x, f, b
Init == /\ x = 0 /\ f = << >> /\ b = EmptyBag
Next == \/ /\ x < 2
           /\ x' = x + 1
           /\ f' = CHOOSE p1 \in {(1 :> 5 + x @@ 3 :> 0), (1 :> 1 @@ 4 :> 0)} : TRUE
           /\ b' = CHOOSE p2 \in {SetToBag({1, 3}) \oplus SetToBag({1}), SetToBag({1, 4})} : TRUE
        \/ UNCHANGED <<x, f, b>>
Inv == x > 0 => (4 \in DOMAIN f /\ 4 \in DOMAIN b)
====
