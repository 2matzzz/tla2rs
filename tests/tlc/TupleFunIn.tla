---- MODULE TupleFunIn ----
\* A tuple tested for membership in a set written out that holds functions over a model value or a
\* string, or the other way round: TLC asks each element whether it equals the value
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Init == x \in 1..3
Next == x < 3 /\ x' = x + 1
Inv == <<1, x>> \notin {(1 :> 1 @@ m :> x)}
InvFun == (1 :> 1 @@ m :> x) \notin {<<1, x>>}
InvStr == <<x>> \notin {("a" :> x)}
InvConst == <<1, x>> \notin {(1 :> 1 @@ m :> 1), (1 :> 1 @@ m :> 2)}
InvSize == <<1, x, 3>> \notin {(1 :> 1 @@ m :> x)}
====
