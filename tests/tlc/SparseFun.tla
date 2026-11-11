---- MODULE SparseFun ----
\* Functions over part of a large integer type, held as their sorted (key, value) pairs: a domain
\* that grows over a large range ([x \in S |-> e] with S from the state, :>, @@), EXCEPT (also on a
\* function over part of a small type), DOMAIN, application, [D -> R], equality, Permutations, and
\* their order in a set
EXTENDS Integers, TLC, FiniteSets
VARIABLES n, f, g, h
Init == n = 0 /\ f = [i \in {} |-> 0] /\ g = << >> /\ h = << >>
Next == /\ n < 4
        /\ n' = n + 1
        /\ \E k \in {n * 100000, 700000} :
             /\ f' = [i \in DOMAIN f \cup {k} |-> IF i \in DOMAIN f THEN f[i] + 1 ELSE 0]
             /\ g' = [(k :> n) @@ g EXCEPT ![k] = @ + 10, ![0] = @ + 1, ![3] = 99]
             /\ h' = [(n :> 0) @@ h EXCEPT ![n] = @ + 5, ![0] = @ + 1, ![7] = 3]
Inv == /\ \A i \in DOMAIN f : f[i] <= 3
       /\ DOMAIN f = DOMAIN g
       /\ g \in [DOMAIN f -> 10..20]
       /\ (g \in [{0, 700000} -> Nat]) = (DOMAIN g = {0, 700000})
       /\ (CHOOSE e \in {f, g} : TRUE) = f
       /\ Cardinality({f, g}) = IF DOMAIN f = {} THEN 1 ELSE 2
       /\ \A i, j \in DOMAIN f : Cardinality(Permutations({i, j})) = IF i = j THEN 1 ELSE 2
       /\ \A e \in [DOMAIN f -> {0}] : e = [i \in DOMAIN f |-> 0]
       /\ \A i \in DOMAIN h : h[i] \in 5..9
\* Violated: the counterexample prints these functions
Small == Cardinality(DOMAIN f) < 3
====
