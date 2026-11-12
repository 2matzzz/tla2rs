---- MODULE SeqAtom ----
\* A variable holding tuples of different lengths or a model value: the tuples are a sequence, the
\* model value is beside it. The type invariant lists them, and is checked on each state
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Keys, Vals, None
VARIABLE req, out, phase, seen
TypeOK == /\ req \in {<<k>> : k \in Keys} \cup {<<k, v>> : k \in Keys, v \in Vals} \cup {None}
          /\ out \in Vals \cup {"done", None}
          /\ phase \in {"idle", "busy"}
Init == /\ req = None
        /\ out = None
        /\ phase = "idle"
        /\ seen = {None}
Ask(r) == /\ phase = "idle"
          /\ req' = r
          /\ out' = None
          /\ phase' = "busy"
          /\ seen' = seen \cup {r}
Answer == /\ phase = "busy"
          /\ req /= None
          /\ out' = IF Len(req) = 2 THEN req[2] ELSE "done"
          /\ phase' = "idle"
          /\ UNCHANGED <<req, seen>>
Next == \/ \E k \in Keys : \/ Ask(<<k>>)
                           \/ \E v \in Vals : Ask(<<k, v>>)
        \/ Answer
Few == Cardinality(seen) < 4
FirstKey == req = None \/ req[1] \in Keys
====
