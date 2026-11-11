---- MODULE RejSanyTlcOps ----
\* :> and @@ are defined in TLC: SANY refuses them in a module that does not extend it
EXTENDS Naturals
VARIABLE f
Init == f = (1 :> 0) @@ (2 :> 0)
Next == UNCHANGED f
====
