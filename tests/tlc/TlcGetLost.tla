---- MODULE TlcGetLost ----
\* Behaviors TLC cannot rebuild, in a spec that reads TLCGet: what B yields depends on a register
\* that goes on growing, so B yields other states when TLC evaluates the steps again to show a
\* behavior, and TLC looks each state up as it goes. A step before the state being expanded that
\* yields no such state stops it with exit 1 and that state's fingerprint (TlcGetLost-Pre), and
\* so does the step to the state being expanded (TlcGetLost) or to its successor
\* (TlcGetLost-Succ), with that state. When Init does not yield the first state (TlcGetLost-Init*,
\* TlcGetLost-Deadlock), or the step from an initial state being expanded does not yield the next
\* (TlcGetLost-First*, TlcGetLost-Eval*), TLC stops showing the behavior and goes on; with
\* -continue it then fails on a NullPointerException
EXTENDS Integers, TLC
VARIABLE x
ASSUME TLCSet(1, 0)
Bump == TLCSet(1, TLCGet(1) + 1)
C(w) == PrintT(<<w, x, TLCGet(1)>>)
Init == x = 0 /\ C("init")
InitR == Bump /\ x = TLCGet(1) /\ C("init")
A == x < 1000 /\ C("A") /\ x' = x + 1
B == x < 1000 /\ Bump /\ C("B") /\ x' = x + 100 * TLCGet(1)
Next == B \/ A
NextD == x < 3 /\ C("D") /\ x' = x + 1
Lost == x # 101
Pre == x # 303
Succ == x # 301
InitLost == x # 3
First == x # 100
Eval == 1 \div (100 - x) >= -1
====
