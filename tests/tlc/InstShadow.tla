---- MODULE InstShadow ----
\* A definition of an instantiated module may name a parameter, a bound variable or a LET
\* definition like a definition written after it (also one of a module it instantiates), or like
\* a name its substitutions read: there the name is still the local one
EXTENDS Integers, TLC
CONSTANT Base
VARIABLE n
INSTANCE InstShadowDefs WITH Offset <- Base
Init == n = 0
Next == n' = Bump(n) % 4 /\ PrintT(<<Small(0..n), Double(n), Sum(n), Shift(n), Twice(n)>>)
====
