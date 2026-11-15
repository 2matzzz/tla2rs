---- MODULE AgainInit ----
\* With -continue, an initial state that violates invariants and comes before one that fails to
\* evaluate an invariant: TLC reports the violations, then the error, and in the pass that computes
\* and checks the initial states again (see PrintAgain) it reports the violations again and goes
\* on, up to the error. AgainInit-Quiet prints nothing
EXTENDS Integers, TLC
VARIABLE x
Init == x \in {0, 1, 2} /\ PrintT(<<"init", x>>)
Next == x' = x
NotZero == PrintT(<<"nz", x>>) /\ x # 0
Positive == PrintT(<<"pos", x>>) /\ x > 0
Bad == PrintT(<<"bad", x>>) /\ 1 \div (1 - x) >= 0
InitQ == x \in {0, 1, 2}
NotZeroQ == x # 0
BadQ == 1 \div (1 - x) >= 0
====
