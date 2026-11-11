This text comes before the module header. TLC ignores it, so it need not be TLA+: "an unclosed
quote, (* an unclosed comment.
------------------------------- MODULE Proofs -------------------------------
(* Theorems, proofs, USE and HIDE are parsed and not evaluated. (* Comments nest. *) *)
EXTENDS Naturals
VARIABLE x
LOCAL Step(a) == (a + 1) % 3
Init == x = 0
Next == x' = Step(x)
TypeOK == x \in 0..2
THEOREM Safe == Init => TypeOK
  <1>1. Init => x = 0
    BY DEF Init
  <1>2. QED
    BY <1>1 DEF TypeOK
LEMMA Trivial == TRUE
  OBVIOUS
PROPOSITION P1 == TRUE
  PROOF OMITTED
COROLLARY C1 == TRUE
  PROOF
    <1> QED OBVIOUS
THEOREM ASSUME NEW n \in Nat PROVE n + 0 = n
  OBVIOUS
AXIOM Ax == TRUE
USE DEF Init
HIDE DEF Init
-----------------------------------------------------------------------------
Inv == x < 3
=============================================================================
Text after the end is ignored too: "another unclosed quote
