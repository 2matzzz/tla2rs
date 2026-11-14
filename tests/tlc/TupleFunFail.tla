---- MODULE TupleFunFail ----
\* A tuple compared with a function over a model value or a string: TLC's comparison fails
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Init == x \in 1..3
Next == x < 3 /\ x' = x + 1
Inv == <<1, x>> # (1 :> 1 @@ m :> x)
InvStr == <<x>> # ("a" :> x)
InvLate == x = 2 => <<1, x>> # (1 :> 1 @@ m :> x)
InvFunLeft == (1 :> 1 @@ m :> x) # <<1, x>>
\* Sizes that differ make them unequal; the keys are walked in TLC's order
InvSize == <<1, x, 3>> # (1 :> 1 @@ m :> x)
InvOrder == (2 :> 1 @@ m :> x) # <<1, x>>
NextEq == x < 3 /\ x' = x + 1 /\ <<x>> # ("a" :> x)
====
