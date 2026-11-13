---- MODULE TlcGet ----
\* TLCGet("level"), ("diameter"), ("distinct") and ("queue") where TLC evaluates them: the ASSUMEs,
\* Init, the actions, the invariants and the CONSTRAINT, and again while it shows a behavior
EXTENDS Naturals, TLC
VARIABLE x
Counts(w) == PrintT(<<w, TLCGet("level"), TLCGet("diameter"), TLCGet("distinct"), TLCGet("queue")>>)
Level == TLCGet("level")
ASSUME Counts("assume")
Init == /\ Counts("init0") /\ x \in {0, 1} /\ Counts("init1")
A == /\ Counts("a0") /\ x < 5 /\ x' = x + 2 /\ Counts("a1")
B == /\ Counts("b0") /\ x < 5 /\ x' \in {x + 3, x + 4} /\ Counts("b1")
Next == A \/ B
Inv == Counts("inv") /\ x # 6
Small == Counts("con") /\ x < 8
Always == Counts("inv")
Stopping == /\ Counts("n") /\ x < 3 /\ x' = x + 1
Failing == /\ Counts("n") /\ x' = x + 1 /\ 10 \div (3 - x') > 0 /\ Counts("n1")
Exiting == /\ Counts("n") /\ x < 9 /\ x' \in {x + 2, x + 3, x + 4} /\ (x' = 2 => TLCSet("exit", TRUE)) /\ Counts("n1")
InitExit == /\ x \in {0, 1, 2} /\ (x = 1 => TLCSet("exit", TRUE)) /\ Counts("i")
\* A bait invariant: violated once the search is deep enough
Bait == Level < 3
\* A next-state relation that changes with the level
Climb == /\ Counts("c") /\ IF Level >= 2 THEN x' = x ELSE x' = x + 1
Ok == x' <= 4
====
