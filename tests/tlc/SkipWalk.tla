---- MODULE SkipWalk ----
\* A walk in a cube that steps one or two cells along an axis, so most cells are reached by paths
\* of different lengths. With several workers the search reaches many cells first by a longer path
\* and must lower their depths later; the counts and the state graph stay those of TLC
EXTENDS Naturals
N == 24
VARIABLES x, y, z
TypeOK == x \in 0..N /\ y \in 0..N /\ z \in 0..N
Init == x = 0 /\ y = 0 /\ z = 0
Step(k) == \/ x + k <= N /\ x' = x + k /\ UNCHANGED <<y, z>>
           \/ y + k <= N /\ y' = y + k /\ UNCHANGED <<x, z>>
           \/ z + k <= N /\ z' = z + k /\ UNCHANGED <<x, y>>
Next == Step(1) \/ Step(2)
====
