---- MODULE EmptyTupleIntoFuns ----
\* The empty tuple from a variable that holds only it, and a set of it, placed where a function
\* over part of a domain (or a set of them) is expected: TLC prints <<>> there, alone, in a set
\* with a function and in ToString
EXTENDS Naturals, TLC
VARIABLES e, u, p, s, n
Init == /\ e = <<>>
        /\ u = {<<>>}
        /\ p = 4 :> 1
        /\ s = {4 :> 1}
        /\ n = 0
Next == /\ n < 4
        /\ n' = n + 1
        /\ UNCHANGED <<e, u>>
        /\ p' = IF n % 2 = 0 THEN e ELSE 4 :> 1
        /\ s' = CASE n = 0 -> u
                  [] n = 1 -> u \cup {4 :> 1}
                  [] n = 2 -> {e, 4 :> 1}
                  [] OTHER -> {4 :> 1} \cup u
        /\ PrintT(<<p', s'>>)
Inv == /\ ToString(p) = IF n % 2 = 1 THEN "<<>>" ELSE "(4 :> 1)"
       /\ ToString(s) = <<"{(4 :> 1)}", "{<<>>}", "{<<>>, (4 :> 1)}", "{<<>>, (4 :> 1)}", "{<<>>, (4 :> 1)}">>[n + 1]
InvViol == n < 4
====
