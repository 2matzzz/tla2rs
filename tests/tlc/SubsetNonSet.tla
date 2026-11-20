---- MODULE SubsetNonSet ----
\* A value that is not a set tested for membership in SUBSET T: TLC stops with "Attempted to check
\* if the non-enumerable value", the value and SUBSET T enumerated, and a fingerprint error when
\* SUBSET T is written where it is tested (not when it comes from a constant definition, nor in an
\* invariant on a successor)
EXTENDS Naturals, TLC
CONSTANT None
VARIABLE x
Subs == SUBSET {1, 2}
InitModel == x = None
InitInt == x = 1
InitStr == x = "a"
InitTup == x = <<1, 2>>
InitRec == x = [a |-> 1]
InitFun == x = (3 :> 1)
InitBool == x = TRUE
InitSet == x = {1}
Next == x' = None
Inv == x \in SUBSET {1, 2}
InvDef == x \in Subs
====
