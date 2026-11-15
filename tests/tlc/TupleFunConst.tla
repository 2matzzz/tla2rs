---- MODULE TupleFunConst ----
\* A membership test of constants where a tuple meets functions over keys that are not all
\* integers: TLC evaluates it where it is written, in Init, an action or an invariant
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Deep == {(m :> 1), (2 :> 1), (3 :> 1)}
T == <<1>>
Init == x = 0
Next == x < 2 /\ x' = x + 1
InitIn == x = 0 /\ <<1>> \notin Deep
NextIn == x < 2 /\ <<1>> \notin Deep /\ x' = x + 1
Inv == <<1>> \notin Deep
InvIn == <<1>> \in Deep
InvLit == <<1>> \notin {(m :> 1)}
InvFun == (1 :> 1 @@ m :> 1) \notin {<<1, 1>>}
\* A tuple from a definition was not built there: no fingerprint error
InvDef == T \notin Deep
\* On a successor TLC gives the message alone
InvLate == x = 1 => <<1>> \notin Deep
InvLateLit == x = 1 => <<1>> \notin {(m :> 1)}
InvLateApp == x = 1 => <<5, 6, 7>>[x + 4] > 0
InvVar == <<x>> \notin Deep
====
