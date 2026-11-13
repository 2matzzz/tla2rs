---- MODULE TlcGetReg ----
\* TLC's registers, TLCSet(i, v) and TLCGet(i): one store that the ASSUMEs, Init, the actions and
\* the invariants share, in the order TLC evaluates them, also while it shows a behavior
EXTENDS Naturals, TLC
VARIABLE x
ASSUME TLCSet(1, 100)
ASSUME PrintT(<<"assume", TLCGet(1)>>)
Init == /\ PrintT(<<"init0", TLCGet(1)>>) /\ TLCSet(1, TLCGet(1) + 1) /\ TLCSet(2, 7) /\ x \in {0, 1} /\ PrintT(<<"init1", TLCGet(1)>>)
Next == /\ PrintT(<<"n0", TLCGet(1), TLCGet(2)>>) /\ TLCSet(1, TLCGet(1) + 1) /\ x < 4 /\ x' = x + 1 /\ PrintT(<<"n1", TLCGet(1)>>)
Inv == /\ PrintT(<<"inv", x, TLCGet(1)>>) /\ TLCSet(1, TLCGet(1) + 10) /\ x # 3
\* Counting the states each action leads to, by register
Count == /\ x < 4 /\ x' \in {x + 1, x + 2} /\ TLCSet(10 + x', TLCGet(10 + x') + 1) /\ PrintT(<<x', TLCGet(10 + x')>>)
Zero == /\ x = 0 /\ \A i \in 10..15 : TLCSet(i, 0)
Seen == PrintT(<<"seen", TLCGet(10 + x)>>)
\* A register never set
Unset == /\ x < 4 /\ x' = x + 1 /\ PrintT(TLCGet(3))
====
