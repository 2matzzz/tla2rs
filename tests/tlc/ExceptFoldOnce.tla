---- MODULE ExceptFoldOnce ----
\* A constant argument used twice, and a LET definition, with an EXCEPT TLC warns about: TLC
\* evaluates each once for the evaluation of the call or the LET, where first used, so it warns
\* once before the line the action prints (and again, without its note, on the next state); the
\* value an EXCEPT changes keeps where it is written when it is an argument
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Two(g) == g[1] + g[2]
Next == /\ Two([<<1, 2>> EXCEPT ![4] = 0]) = 3
        /\ PrintT(x)
        /\ x' = (x + 1) % 3
NextLet == LET f == [<<1, 2>> EXCEPT ![3] = 0] IN
           /\ f[1] = 1
           /\ PrintT(x)
           /\ f[2] = 2
           /\ x' = (x + 1) % 3
Upd(h, k) == [h EXCEPT ![k] = 0]
NextUpd == /\ Upd(<<4>>, 2)[1] = 4
           /\ PrintT(x)
           /\ x' = (x + 1) % 3
====
