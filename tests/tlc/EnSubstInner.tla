---- MODULE EnSubstInner ----
\* Actions over a variable that EnSubst substitutes, and whether they are enabled, written here
EXTENDS Naturals
VARIABLE sum, k
Keep == k' = 1 - k /\ sum' = sum
Bump == k' = 1 - k /\ sum' = sum + 1
None == k' = 1 - k /\ sum' \in {}
Pick == k' = 1 - k /\ sum' \in {7, 8}
Twice == k' = 1 - k /\ sum' = 4 /\ sum' = 5
Reread == k' = 1 - k /\ sum' = 9 /\ sum' > 3
Same == k' = 1 - k /\ UNCHANGED sum
Early == k' = 1 - k /\ sum' > 3
WKeep == WF_sum(Keep)
WBump == WF_sum(Bump)
ENone == []<>ENABLED None
EPick == []<>ENABLED Pick
ETwice == []<>ENABLED Twice
EReread == []<>ENABLED Reread
ESame == []<>ENABLED Same
EEarly == []<>ENABLED Early
====
