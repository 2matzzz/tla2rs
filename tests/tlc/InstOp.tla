---- MODULE InstOp ----
\* Instances that substitute an operator for an operator constant: a defined operator and a LAMBDA
EXTENDS Naturals
VARIABLE n
Double(x) == 2 * x
D == INSTANCE Scaled WITH F <- Double, v <- n
T == INSTANCE Scaled WITH F <- LAMBDA x : 3 * x, v <- n
Init == D!Init
Next == D!Next
Inv == ~D!Big \/ ~T!Big
====
