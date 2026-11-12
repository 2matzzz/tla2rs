---- MODULE CmCase ----
\* A CASE of a CommunityModules definition with no true condition (Interleave of sequences of
\* different lengths): TLC names the position of the CASE in the release's SequencesExt
EXTENDS Naturals, Sequences, SequencesExt, TLC
VARIABLES s, out
Init == s = <<1>> /\ out = <<>>
Next == Len(s) < 3 /\ s' = Append(s, Len(s) + 1) /\ out' = Interleave(s', <<7, 8>>)
Grow == Len(s) < 3 /\ s' = Append(s, Len(s) + 1) /\ out' = <<>>
Inv == Len(s) < 2 \/ Len(Interleave(s, <<7, 8>>)) > 0
InitBad == s = <<1>> /\ out = Interleave(s, <<>>)
====
