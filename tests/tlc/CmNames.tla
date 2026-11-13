---- MODULE CmNames ----
\* Strings equal to names of modules of the CommunityModules that only those modules (or the
\* modules they read) write: TLC creates them when it parses the release's modules, before the
\* strings of the spec
EXTENDS SequencesExt
VARIABLE w
Words == {"zz", "Len", "SetToSeq", "MapThenFoldSet", "Cardinality", "BagToSet", "Restrict"}
ASSUME PrintT(Words)
ASSUME PrintT(<<CHOOSE s \in Words : TRUE, SetToSeq(Words)>>)
Init == w \in Words
Next == UNCHANGED w
Shown == PrintT(w)
====
