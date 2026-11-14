---- MODULE EmptyTupleShow ----
\* Empty tuples held in the state, in a spec that builds no empty function: TLC prints <<>> for
\* each, alone, in a set, a function and a tuple, in PrintT and in ToString
EXTENDS Naturals, TLC
VARIABLES e, s, f, p, n
Init == /\ e = <<>>
        /\ s = {<<>>}
        /\ f = [i \in 1..2 |-> <<>>]
        /\ p = <<<<>>, 0>>
        /\ n = 0
Next == /\ n < 2
        /\ n' = n + 1
        /\ p' = <<<<>>, n + 1>>
        /\ UNCHANGED <<e, s, f>>
        /\ PrintT(<<e, s, f, p>>)
Inv == /\ ToString(e) = "<<>>"
       /\ ToString(<<s, f>>) = "<<{<<>>}, <<<<>>, <<>>>>>>"
       /\ ToString(p) = <<"<<<<>>, 0>>", "<<<<>>, 1>>", "<<<<>>, 2>>">>[n + 1]
InvViol == ToString(p) # "<<<<>>, 2>>"
====
