---- MODULE TupleFunOrder ----
\* A tuple against a function when the compiler orders values (issue #123): TLC compares a tuple as
\* the function over 1..n, by the size of the domain, then key and value pair by pair
EXTENDS Naturals, TLC
ASSUME PrintT({<<5>>, (2 :> 1)})
ASSUME PrintT({<<2>>, (2 :> 1)})
ASSUME PrintT({<<5>>, (0 :> 9 @@ 1 :> 9)})
ASSUME PrintT({<<5>>, (1 :> 5 @@ 3 :> 0), <<5, 0>>})
ASSUME PrintT({(1 :> 9 @@ 2 :> 0), (1 :> 5 @@ 3 :> 0)})
ASSUME PrintT(CHOOSE s \in {<<5>>, (2 :> 1)} : TRUE)
====
