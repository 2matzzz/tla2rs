---- MODULE PrintLevel ----
\* SANY takes the level of Print and PrintT from their definitions in TLC.tla, `Print(out, val) ==
\* val` and `PrintT(out) == TRUE`: what they print is not counted. So in a temporal formula,
\* `PrintT(x)` and `Print(x', TRUE)` are of constant level, and TLC evaluates them as constants
\* when it converts the formula, before the ASSUMEs, stopping on the variable (exit 151).
\* `Print(x, TRUE)` under [] is checked as an invariant, and `Print(x', x < 5)` is a state
\* predicate, which fails while checking liveness
EXTENDS Naturals, TLC
VARIABLE x
Shown == PrintT("constant definition")
ASSUME PrintT("assume")
Init == x = 0 /\ PrintT(<<"init", x>>)
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x /\ WF_x(Next)
ConstVar == <>(PrintT(x) /\ x = 1)
ConstPrime == <>(Print(x', TRUE) /\ x = 1)
Before == <>(PrintT("before") /\ x = 1)
Inv == [](Print(<<"inv", x>>, TRUE))
StatePrime == <>[](Print(<<"state", x'>>, x < 5))
\* Accepted by SANY, though nothing checks it: the level of `Print(x', TRUE)` is constant
Unchecked == <>Print(x', TRUE)
====
