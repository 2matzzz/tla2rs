---- MODULE EmptyFunJoin ----
\* An empty function in Init is a value of the type of the function a later step assigns: over
\* another domain (:>, @@), over 1..n, and next to <<>>. TLC prints it as << >> and the tuple as <<>>
EXTENDS Naturals, TLC
VARIABLE p
Init == p = [i \in {} |-> {}]
Next == p' = 4 :> 1..3
NextAtAt == p' = (4 :> 1..3) @@ (5 :> {})
NextSeq == p' = [i \in 1..2 |-> {}]
NextEq == p' = IF p = <<>> THEN 4 :> 1..3 ELSE <<>>
NextShow == /\ p' = IF p = <<>> THEN 4 :> 1..3 ELSE <<>>
            /\ PrintT(p)
Inv == p = <<>>
====
