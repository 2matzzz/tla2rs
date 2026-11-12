---------------------------- MODULE PcalSumInst ----------------------------
\* TLC does not check a module it only instantiates
VARIABLES x, y, pc
I == INSTANCE PcalSumAlg
Init == I!Init
Next == I!Next
=============================================================================
