---- MODULE SanyScope ----
\* SANY puts a name in scope only after the statement that declares or defines it (measured on SANY 2.19)
EXTENDS Naturals, SanyScopeLeft, SanyScopeRight
\* Parameters and bound variables named like a VARIABLE, CONSTANT or definition that comes later
Double(w) == 2 * w
Above(lim) == \E lim2 \in {lim} : \E w \in {lim2} : w > 0
Plus(Later) == Later + 1
Bump(n) == LET lim == n + 1 IN lim
\* A definition's own name is not in scope in its body; a LOCAL definition of an extended module is not in scope here
Self == \E Self \in {1} : Self = 1
Hidden(Int) == Int + 1
VARIABLE w
CONSTANT lim
Later == 3
\* The definitions of a module without constants or variables, extended and instantiated: one symbol
INSTANCE SanyScopeBase
\* The same name in sibling scopes, and labels that list the bound variables around them
Twice == (LET k == 1 IN k) + (LET k == 2 IN k)
Ordered == \E i \in {1} : \A j \in {2} : step(j, i) :: i < j
Init == w = 0
Next == w' = (Double(w) + Plus(Later) + Bump(lim) + Hidden(Shared) + FromLeft + FromRight) % 5
Inv == Self /\ Ordered /\ Above(1) /\ Twice = 3
====
