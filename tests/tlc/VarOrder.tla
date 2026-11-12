---- MODULE VarOrder ----
\* TLC prints the variables of a state in the order of SANY's table of the root module's names, a
\* Java hash table keyed by name: here flag, pc, turn, count, total, queue, neither the order
\* declared nor that of the names. Missing assignments are listed in that order too
EXTENDS Naturals, Sequences
VARIABLES count, total, queue, pc, turn, flag
Init == /\ count = 0 /\ total = 0 /\ queue = <<>>
        /\ pc = "start" /\ turn = 1 /\ flag = FALSE
Next == /\ count < 3
        /\ count' = count + 1
        /\ total' = total + count
        /\ queue' = Append(queue, count)
        /\ pc' = IF count = 2 THEN "done" ELSE "run"
        /\ turn' = 3 - turn
        /\ flag' = ~flag
Partial == /\ count < 2
           /\ flag' = ~flag
           /\ pc' = pc
           /\ total' = total + 1
           /\ queue' = queue
Small == total < 3
====
