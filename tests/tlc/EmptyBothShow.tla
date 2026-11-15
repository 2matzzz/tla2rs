---- MODULE EmptyBothShow ----
\* Empty tuples and empty functions in one spec. TLC prints <<>> for the tuple and << >> for a
\* function, also once a function over part of a domain becomes empty (p over a small domain, q
\* over a large one, whose strings are too many for ToString), in states, PrintT and ToString.
\* The two are equal, so a set holding both keeps the one written first
EXTENDS Naturals, TLC
VARIABLES p, q, e, s, t, n
Init == /\ p = 4 :> 1
        /\ q = [i \in {1, 70000} |-> i]
        /\ e = <<>>
        /\ s = {<<>>, [i \in {} |-> 1]}
        /\ t = <<>>
        /\ n = 0
Next == /\ n < 4
        /\ n' = n + 1
        /\ p' = CASE n = 0 -> [i \in DOMAIN p \ {4} |-> p[i]]
                  [] n = 1 -> <<>>
                  [] n = 2 -> 4 :> 1
                  [] OTHER -> [i \in {} |-> 1] @@ [i \in {} |-> 2]
        /\ q' = IF n % 2 = 0 THEN [i \in DOMAIN q \ {1, 70000} |-> q[i]] ELSE <<>>
        /\ e' = IF n % 2 = 0 THEN [i \in {} |-> 1] ELSE <<>>
        /\ s' = IF DOMAIN p' = {} THEN {e', p'} ELSE {e'}
        /\ t' = <<ToString(p'), ToString(e'), ToString(s')>>
        /\ PrintT(<<p', q', e', s', {p', e'}>>)
Inv == /\ ToString(p) = <<"(4 :> 1)", "<< >>", "<<>>", "(4 :> 1)", "<< >>">>[n + 1]
       /\ ToString(e) = <<"<<>>", "<< >>", "<<>>", "<< >>", "<<>>">>[n + 1]
       /\ ToString(s) = <<"{<<>>}", "{<< >>}", "{<<>>}", "{<< >>}", "{<<>>}">>[n + 1]
InvViol == n < 4
====
