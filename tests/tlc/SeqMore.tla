---- MODULE SeqMore ----
\* Sequences inside records, functions, and sets; a tuple and a function over 1..n are the same
\* value as a sequence; SYMMETRY permutes inside sequences
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Procs
VARIABLES log, seen, last
TypeOK == /\ log \in [Procs -> Seq(Procs)]
          /\ seen \subseteq Seq(Procs)
          /\ last \in [who : Procs \cup {"none"}, path : Seq(Procs)]
Init == /\ log = [p \in Procs |-> <<>>]
        /\ seen = {}
        /\ last = [who |-> "none", path |-> <<>>]
Next == \E p, r \in Procs :
          /\ Len(log[p]) < 2
          /\ log' = [log EXCEPT ![p] = Append(@, r)]
          /\ seen' = seen \cup {log'[p]}
          /\ last' = [who |-> p, path |-> <<r>> \o log[p]]
Inv == /\ \A p \in Procs : log[p] = [k \in 1..Len(log[p]) |-> log[p][k]]
       /\ \A s \in seen : Len(s) \in 1..2
       /\ <<>> \notin seen
       /\ \A p \in Procs : Len(log[p]) = 2 => log[p] \in {<<a, b>> : a, b \in Procs}
       /\ last.path = <<>> \/ Head(last.path) \in Procs
       /\ Len("abc") = 3 /\ <<1, 2>> = [i \in 1..2 |-> i] /\ <<1>> # <<1, 1>>
       /\ (IF Len(last.path) > 0 THEN last.path[Len(last.path)] ELSE "none") # "x"
Bound == \A p \in Procs : Len(log[p]) <= 2
Sym == Permutations(Procs)
\* Violated
Small == Cardinality(seen) < 3
====
