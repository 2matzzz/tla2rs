---- MODULE ExtTypeBase ----
\* A module whose type invariant ExtType extends without updating it
EXTENDS Naturals
VARIABLE cell
TypeInv == cell \in [level : 0..2]
====
