---- MODULE EmptyFunShow ----
\* Empty functions held in the state, in a spec that builds no empty tuple: TLC prints << >> for
\* each, alone, in a set, a record, a function and an optional field of a record, in PrintT and
\* in ToString
EXTENDS Naturals, TLC
VARIABLES e, s, r, f, o, n
Init == /\ e = [i \in {} |-> 1]
        /\ s = {[i \in {} |-> 1]}
        /\ r = [a |-> [i \in {} |-> 1]]
        /\ f = [i \in 1..2 |-> [j \in {} |-> 1]]
        /\ o = [k |-> 0]
        /\ n = 0
Next == /\ n < 2
        /\ n' = n + 1
        /\ o' = IF n = 0 THEN [k |-> 1, v |-> 4 :> 1] ELSE [k |-> 2, v |-> [i \in {} |-> 1]]
        /\ UNCHANGED <<e, s, r, f>>
        /\ PrintT(<<e, s, r, f, o>>)
Inv == /\ ToString(e) = "<< >>"
       /\ ToString(<<s, r, f>>) = "<<{<< >>}, [a |-> << >>], <<<< >>, << >>>>>>"
       /\ ToString(o) = <<"[k |-> 0]", "[k |-> 1, v |-> (4 :> 1)]", "[k |-> 2, v |-> << >>]">>[n + 1]
InvViol == ToString(o) # "[k |-> 2, v |-> << >>]"
====
