---- MODULE TlcGetReplay ----
\* The passes TLC makes again after an evaluation error (see PrintAgain, AgainCon, TlcGetAgain) in
\* a spec that reads TLCGet: they handle each state as it is computed, at level 0 for the
\* successors, and the registers go on changing, so B and InitR yield states the first pass did
\* not. TLC adds and queues them, as the counts it reads and prints show, and checks their
\* invariants: one that fails to evaluate again is reported as in AgainTwice, and an initial state
\* that violates an invariant is reported, with -continue also one the first pass reported (TLC
\* then exits with 0 unless the pass stops at an error, and counts what this pass generated).
\* B stops changing once the register passes 4, so that the behaviors are rebuilt
EXTENDS Integers, TLC
VARIABLE x
ASSUME TLCSet(1, 0)
Bump == TLCSet(1, TLCGet(1) + 1)
Reg == IF TLCGet(1) > 4 THEN 4 ELSE TLCGet(1)
C(w) == PrintT(<<w, x, TLCGet(1), TLCGet("level"), TLCGet("distinct"), TLCGet("queue")>>)
Init == x \in {0, 1} /\ C("init")
A == x < 50 /\ C("A") /\ x' = x + 2
B == x < 50 /\ Bump /\ C("B") /\ x' = x + 10 * Reg
Next == B \/ A
Ok == C("ok")
Bad == C("bad") /\ 1 \div (3 - x) >= -1
BadTwice == C("bad") /\ 1 \div ((3 - x) * (41 - x)) >= -1
Cons == C("cons") /\ 1 \div (3 - x) >= -1
InitR == Bump /\ x \in {TLCGet(1), TLCGet(1) + 10} /\ C("init")
InitG == Bump /\ x \in {TLCGet(1), 5} /\ C("init")
NotZero == C("nz") /\ x # 0
BadInit == C("bad") /\ 1 \div (1 - x) >= 0
BadInitTwice == C("bad") /\ 1 \div ((1 - x) * (2 - x)) >= -1
BadInitG == C("bad") /\ 1 \div ((5 - x) * (2 - x)) >= -1
====
