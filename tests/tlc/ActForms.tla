---- MODULE ActForms ----
\* Action forms TLC handles: \A over a constant set (a conjunction that can assign), [A]_v,
\* UNCHANGED of an expression (e' = e, an error while a variable in it is undetermined), a primed
\* constant, ENABLED in an action and in Init
EXTENDS Naturals
CONSTANT K
VARIABLES x, y, f
vars == <<x, y, f>>
Init == x = 0 /\ y = 0 /\ f = [i \in 1..2 |-> 0]
Inc == x' = (x + 1) % 3 /\ UNCHANGED <<y, f>>
NAll == \A i \in {1} : x' = (x + i) % 3 /\ y' = y /\ f' = f
NAllTwo == \A i \in {1, 2} : x' = (x + 1) % 3 /\ UNCHANGED <<y, f>>
NAllMulti == \A i \in {0, 1}, j \in {2} : x' = (x + 1) % 3 /\ y' = (y + i * j) % 3 /\ f' = f
NAllFn == x' = (x + 1) % 3 /\ y' = y /\ \A i \in {1, 2} : f'[i] = (f[i] + i) % 2
NBox == [Inc]_vars
NBoxY == [Inc]_<<x>> /\ UNCHANGED <<y, f>>
NUnchFirst == UNCHANGED f[1] /\ x' = (x + 1) % 3 /\ y' = y /\ f' = f
NUnchSum == x' = (x + 1) % 3 /\ UNCHANGED (x + y) /\ y' = y /\ f' = f
NUnchMix == x' = (x + 1) % 3 /\ UNCHANGED <<y, f[1], f>>
NUnchAfter == Inc /\ UNCHANGED f[1] /\ UNCHANGED (x + y - x)
NUnchAfterBad == Inc /\ UNCHANGED (x * 0 + 1 + x)
NConstPrime == K' = K /\ Inc
NConstEq == Inc /\ K' = 2
NEnabled == ENABLED Inc /\ Inc
NEnabledP == ENABLED (x' = 1) /\ Inc
InitAll == \A i \in {0} : x = i /\ y = i /\ f = [j \in 1..2 |-> i]
InitEn == x = 0 /\ y = 0 /\ f = [i \in 1..2 |-> 0] /\ ENABLED Inc
InitEnFirst == ENABLED Inc /\ x = 0 /\ y = 0 /\ f = [i \in 1..2 |-> 0]
Inv == x < 2
====
