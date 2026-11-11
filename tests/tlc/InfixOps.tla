---- MODULE InfixOps ----
\* Infix operators defined by the spec, and :> / @@ from the TLC module
EXTENDS Naturals, TLC
CONSTANTS Procs
VARIABLES cnt, acc
a \oplus b == (a + b) % 4
a ++ b == a \cup b
S ** T == {<<x, y>> : x \in S, y \in T}
a ^^ b == a * b % 4
TypeOK == cnt \in [Procs -> 0..3] /\ acc \subseteq Procs
Init == cnt = [p \in Procs |-> 0] /\ acc = {}
Next == \E p \in Procs :
          /\ cnt' = (p :> cnt[p] \oplus 1) @@ cnt
          /\ acc' = acc ++ {p}
Inv == /\ \A p \in Procs : cnt[p] \oplus 0 = cnt[p]
       /\ (1 :> 2 @@ 2 :> 3)[2] = 3
       /\ (1 :> 2 @@ 1 :> 3)[1] = 2
       /\ acc ** {1} \subseteq Procs \X {1}
       /\ 2 ^^ 3 = 2 /\ 1 \oplus 2 ^^ 3 = 3
\* Violated
Low == \A p \in Procs : cnt[p] < 3
====
