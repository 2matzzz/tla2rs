---- MODULE TupleFunMixed ----
\* A constant set of tuples and functions over keys that are not all integers. When it holds such
\* a function and a tuple of the same size, TLC fails to sort it, builds it again where it is used
\* and asks each element in turn, in the order written; otherwise it searches the sorted set by
\* halves, ordering a tuple and a function by size
EXTENDS Naturals, TLC
CONSTANTS m, k
VARIABLE x
Mix == {(1 :> 1 @@ m :> 1), <<1, 1>>, <<2, 2>>}
\* The tuple is met before the function
First == {<<1, 1>>, (1 :> 1 @@ m :> 1)}
FunLast == {<<2, 2>>, <<1, 1>>, (1 :> 1 @@ m :> 1)}
Sorted == {<<2, 2>>, (1 :> 1 @@ m :> 1 @@ 3 :> 3), <<1, 1>>}
ASSUME k = 1 => <<1, 1>> \in Mix
Init == x = 0
Next == x < 2 /\ x' = x + 1
InitIn == x = 0 /\ <<1, 1>> \in Mix
NextIn == x < 2 /\ <<2, 2>> \in Mix /\ x' = x + 1
Inv == <<1, 1>> \in Mix
InvLate == x = 1 => <<2, 2>> \in Mix
InvFirst == <<1, 1>> \in First /\ <<1, 1>> \in FunLast
InvPast == <<3, 3>> \notin First
InvFun == (1 :> 1 @@ m :> 1) \in FunLast
InvSorted == <<1, 1, 1>> \notin Sorted
InvFunSorted == (m :> 1 @@ 1 :> 1) \notin Sorted
====
