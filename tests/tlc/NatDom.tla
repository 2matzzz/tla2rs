---- MODULE NatDom ----
\* Functions over part of an unbounded type: keys taken from a variable declared in Nat, and keys
\* that are sets, also under SYMMETRY of their values
EXTENDS Integers, TLC, FiniteSets
CONSTANTS Proc
VARIABLES x, f, seen, owner
TypeOK == x \in Nat
Init == x = 0 /\ f = << >> /\ seen = << >> /\ owner = << >>
Next == \/ /\ x' = x + 1
           /\ f' = f @@ (x :> x * x)
           /\ \E p \in Proc :
                /\ seen' = seen @@ ({x, 2 * x} :> <<p, x>>)
                /\ owner' = (x * 70000 :> p) @@ owner
        \/ /\ x' = x + 2
           /\ f' = (x :> 0) @@ f
           /\ UNCHANGED <<seen, owner>>
Con == x < 5
Inv == /\ \A k \in DOMAIN f : f[k] \in {0, k * k}
       /\ \A k \in DOMAIN seen : seen[k][2] \in k
       /\ \A k \in DOMAIN owner : owner[k] \in Proc
       /\ f \in [DOMAIN f -> Nat]
Sym == Permutations(Proc)
\* Violated
Few == Cardinality(DOMAIN seen) < 2
\* TLC cannot compare a finite domain with Nat: an evaluation error
InNat == f \in [Nat -> Nat]
====
