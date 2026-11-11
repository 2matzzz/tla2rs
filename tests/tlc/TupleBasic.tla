---- MODULE TupleBasic ----
\* Tuples as state values: in functions, records, and variables; indexing, EXCEPT into a tuple,
\* comparisons, and a TypeOK over A \X B.
EXTENDS Naturals, Sequences
CONSTANTS Procs
VARIABLES pos, last, edge
TypeOK == /\ pos \in [Procs -> (0..2) \X BOOLEAN]
          /\ last \in Procs \X (0..2)
          /\ edge \in [from : Procs, at : (0..2) \X (0..2)]
P0 == CHOOSE p \in Procs : TRUE
Init == /\ pos = [p \in Procs |-> <<0, FALSE>>]
        /\ last = <<P0, 0>>
        /\ edge = [from |-> P0, at |-> <<0, 0>>]
Step(p) == /\ pos[p][1] < 2
           /\ pos' = [pos EXCEPT ![p][1] = @ + 1, ![p][2] = ~@]
           /\ last' = <<p, pos[p][1] + 1>>
           /\ edge' = [edge EXCEPT !.from = p, !.at = <<pos[p][1], @[1]>>]
Reset(p) == /\ pos[p][1] = 2
            /\ pos' = [pos EXCEPT ![p] = <<0, pos[p] = <<2, FALSE>>>>]
            /\ UNCHANGED <<last, edge>>
Next == \E p \in Procs : Step(p) \/ Reset(p)
Inv == /\ last[2] <= 2
       /\ \A p \in Procs : pos[p] # <<1, TRUE>> \/ pos[p][2]
       /\ edge.at \in (0..2) \X (0..2)
       /\ <<last[1], last[2]>> = last
       /\ DOMAIN last = 1..2 /\ DOMAIN pos[last[1]] = {1, 2}
       /\ \A p \in Procs \X (0..2) : p = last => p[2] = last[2]
\* Violated: the counterexample prints tuples inside a function, a record, and a variable
NeverBoth == ~(pos[last[1]] = <<2, FALSE>> /\ edge.at = <<1, 0>> /\ \E p \in Procs : pos[p] = <<1, TRUE>>)
\* VIEW: a tuple holding a function and a model value
View == <<pos, last[1]>>
====
