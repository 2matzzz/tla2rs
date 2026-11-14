---- MODULE TlcGetAgain ----
\* PrintAgain's pass over the initial states in a spec that reads TLCGet, where each initial state
\* is checked as Init computes it: after an error on an initial state, TLC computes and checks them
\* again from the start up to the error, the same way, printing again; the registers go on changing
\* and the counts stay. After a fingerprint error (TupleFunGet) the first pass then goes on
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
ASSUME TLCSet(1, 0)
Init == x \in {0, 1, 2} /\ TLCSet(1, TLCGet(1) + 1) /\ PrintT(<<"init", x, TLCGet(1), TLCGet("distinct"), TLCGet("queue")>>)
InitErr == Init /\ 1 \div (1 - x) >= 0
Next == x < 9 /\ x' = x + 1
Ok == PrintT(<<"ok", x, TLCGet(1), TLCGet("distinct"), TLCGet("queue")>>)
Bad == PrintT(<<"bad", x, TLCGet(1)>>) /\ TLCSet(1, TLCGet(1) + 10) /\ 1 \div (1 - x) >= 0
Fp == PrintT(<<"fp", x, TLCGet(1)>>) /\ TLCSet(1, TLCGet(1) + 10) /\ (x = 1 => <<1, x>> # (1 :> 1 @@ m :> x))
====
