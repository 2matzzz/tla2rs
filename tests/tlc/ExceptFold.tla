---- MODULE ExceptFold ----
\* An EXCEPT of constant level that names an argument or field the value does not have, inside
\* Init, an action or an invariant: TLC evaluates it there each time and warns (each text twice
\* at most)
EXTENDS Naturals, Sequences
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3 /\ [<<1, 2>> EXCEPT ![3] = 0][1] = 1
Spec == Init /\ [][Next]_vars
Inv == x < 3 /\ [[a |-> 1] EXCEPT !.b = 2].a = 1
InitE == x = [i \in 1..2 |-> 0][1] /\ [[i \in 1..2 |-> i] EXCEPT ![7] = 0][2] = 2
\* An operator with arguments, called with constants
Upd(f, k) == [f EXCEPT ![k] = 0]
NextOp == x' = (x + 1) % 3 /\ Upd([i \in 1..2 |-> i], 5)[1] = 1 /\ Upd(<<4>>, 2)[1] = 4
\* A definition without arguments: TLC warns when it starts, and not where it is used
Zero == [<<1, 2>> EXCEPT ![4] = 0]
NextZero == x' = (x + 1) % 3 /\ Zero[1] = 1
\* Two in one evaluation, the second only in the second disjunct
NextTwo == \/ x' = (x + 1) % 3 /\ [<<1>> EXCEPT ![2] = 0, ![3] = 0][1] = 1
           \/ x' = x /\ [[a |-> 1] EXCEPT !.c = 0].a = 1
\* The condition of an IF in an action and in an expression, and the set of a quantifier
NextIf == /\ IF [<<1>> EXCEPT ![5] = 0][1] = 1 THEN x' = (x + 1) % 3 ELSE x' = 0
          /\ x' = IF [[a |-> 1] EXCEPT !.d = 0].a = 1 THEN x' ELSE 0
          /\ \E i \in DOMAIN [<<1, 2>> EXCEPT ![9] = 0] : i = 1
\* The set of a \A that assigns variables, and the argument of a recursive operator that does
RECURSIVE Step(_)
Step(f) == IF f = <<>> THEN UNCHANGED x ELSE x' = (x + Head(f)) % 3
NextAll == \A i \in DOMAIN [<<1>> EXCEPT ![9] = 0] : x' = (x + i) % 3
NextRec == Step([<<1>> EXCEPT ![8] = 0])
====
