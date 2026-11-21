---- MODULE NeverAdded ----
\* Records and tuples taken from sets that stay empty, since the only action adding to them is
\* disabled by a constant (On = FALSE): their elements have no value, and the code that updates
\* them, builds from them or applies them never runs (issue #136). NeverAdded-On adds to them
EXTENDS Naturals
CONSTANT On
VARIABLES s, t, n
Init == s = {} /\ t = {} /\ n = 0
Add == On /\ n < 2 /\ s' = s \cup {[a |-> n, b |-> 0]} /\ t' = t \cup {<<n, 0>>} /\ n' = n + 1
RecExcept == s # {} /\ s' = {[f EXCEPT !.b = 1] : f \in s} /\ UNCHANGED <<t, n>>
RecBuild == s # {} /\ s' = {[a |-> f.a, b |-> 1] : f \in s} /\ UNCHANGED <<t, n>>
RecTuple == s # {} /\ s' = {[a |-> <<f.a, 1>>[1], b |-> 1] : f \in s} /\ UNCHANGED <<t, n>>
RecDeep == s # {} /\ s' = {[[f EXCEPT !.b = 1] EXCEPT !.a = 2] : f \in s} /\ UNCHANGED <<t, n>>
TupBuild == t # {} /\ t' = {<<f[1], 1>> : f \in t} /\ UNCHANGED <<s, n>>
TupExcept == t # {} /\ t' = {[f EXCEPT ![2] = 1] : f \in t} /\ UNCHANGED <<s, n>>
Next == Add \/ RecExcept \/ RecBuild \/ RecTuple \/ RecDeep \/ TupBuild \/ TupExcept
Spec == Init /\ [][Next]_<<s, t, n>>
====
