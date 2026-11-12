---- MODULE PrintWide ----
\* Print and PrintT pretty-print each value they print, as TLC prints a state: a value wider than
\* 80 columns is broken over lines, in an ASSUME (printed when TLC starts) and in an action
EXTENDS Naturals, TLC
VARIABLE n
Long == [alpha |-> "first value", beta |-> "second value", gamma |-> <<1, 2, 3>>, delta |-> {4, 5}]
ASSUME PrintT(<<"a label that is long", Long>>)
ASSUME Print(<<"short", 1>>, Long) = Long
Init == n = 0
Next == n < 2 /\ n' = n + 1 /\ PrintT([k \in 1..3 |-> <<"element", k + n, Long.alpha>>])
====
