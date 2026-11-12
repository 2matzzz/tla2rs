---- MODULE ExtType ----
\* The records of cell have a field the type invariant of the extended module lacks: tla2rs infers
\* the types from Init and Next instead, and checks TypeInv as an ordinary invariant
EXTENDS ExtTypeBase
Init == cell = [level |-> 0, mark |-> FALSE]
Next == \/ cell.level < 2 /\ cell' = [cell EXCEPT !.level = @ + 1]
        \/ ~cell.mark /\ cell' = [cell EXCEPT !.mark = TRUE]
Low == cell.level < 2 \/ ~cell.mark
====
