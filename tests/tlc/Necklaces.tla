---- MODULE Necklaces ----
\* Membership in a constant set of thousands of words, functions over 0..n-1 (the necklaces of
\* up to 8 beads of 3 colours): one chain of comparisons was too deep for rustc, and a temporary
\* array of the initial states took it minutes
EXTENDS Naturals, FiniteSets
Beads == 0..2
Words == UNION {[0..(n - 1) -> Beads] : n \in 1..8}
VARIABLE w
Init == w \in Words
Next == w' = [i \in DOMAIN w |-> w[(i + 1) % Cardinality(DOMAIN w)]]
Valid == w \in Words
====
