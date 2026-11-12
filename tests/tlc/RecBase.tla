---- MODULE RecBase ----
\* A recursive function whose base case is a function from the state, updated by EXCEPT at each
\* step: its type comes from the base case
EXTENDS Naturals, Sequences
CONSTANT Cells
VARIABLE mem, queue
Applied == LET f[i \in 0..Len(queue)] == IF i = 0 THEN mem ELSE [f[i - 1] EXCEPT ![queue[i][1]] = queue[i][2]]
           IN f[Len(queue)]
Init == mem = [c \in Cells |-> 0] /\ queue = <<>>
Next == \/ Len(queue) < 2 /\ \E c \in Cells, v \in 0..1 : queue' = Append(queue, <<c, v>>) /\ UNCHANGED mem
        \/ queue /= <<>> /\ mem' = [mem EXCEPT ![queue[1][1]] = queue[1][2]] /\ queue' = Tail(queue)
Same == \A c \in Cells : Applied[c] \in 0..1
Settled == Applied = mem
====
