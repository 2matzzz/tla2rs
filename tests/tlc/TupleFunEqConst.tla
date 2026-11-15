---- MODULE TupleFunEqConst ----
\* A constant tuple compared with a constant function over keys that are not all integers: TLC
\* walks the function's keys and fails at one that is not an integer, where it is written
EXTENDS Naturals, TLC
CONSTANTS m, k
VARIABLE x
T == <<1>>
ASSUME k = 1 => <<1>> # (m :> 1)
Init == x = 0
Next == x < 2 /\ x' = x + 1
InitEq == x = 0 /\ <<1>> # (m :> 1)
NextEq == x < 2 /\ <<1>> # ("a" :> 1) /\ x' = x + 1
Inv == <<1>> # (m :> 1)
InvStr == <<1>> # ("a" :> 1)
InvFunLeft == (m :> 1) = <<1>>
InvSet == {<<1>>} # {(m :> 1)}
InvPair == <<1, 1>> = (1 :> 1 @@ m :> 1)
\* A tuple from a definition was not built there
InvDef == T # (m :> 1)
\* Sizes that differ make them unequal
InvSize == <<1, 2>> # (m :> 1)
InvLate == x = 1 => <<1>> # (m :> 1)
====
