---- MODULE TupleFunNest ----
\* A tuple inside a tuple, a record or a set, compared with a function over a model value there
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Init == x \in 1..3
Next == x < 3 /\ x' = x + 1
Inv == <<<<1, x>>>> # <<(1 :> 1 @@ m :> x)>>
InvRight == <<(1 :> 1 @@ m :> x)>> # <<<<1, x>>>>
\* The parts are compared in order, and the first that differs makes them unequal
InvShort == <<2, <<1, x>>>> # <<3, (1 :> 1 @@ m :> x)>>
InvRec == [a |-> <<1, x>>, b |-> 2] # [a |-> (1 :> 1 @@ m :> x), b |-> 3]
InvRecLate == [a |-> 2, b |-> <<1, x>>] # [a |-> 3, b |-> (1 :> 1 @@ m :> x)]
InvSet == {<<1, x>>} # {(1 :> 1 @@ m :> x)}
InvSetTwo == {<<1, x>>, <<2, x>>} # {(1 :> 1 @@ m :> x), (1 :> 2 @@ m :> x)}
InvSetSize == {<<1, x>>, <<2, x>>} # {(1 :> 1 @@ m :> x)}
====
