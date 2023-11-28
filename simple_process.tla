---- MODULE simple_process ----
EXTENDS TLC, Naturals

ProcSet == {0,1}

VARIABLE pc
VARIABLE barrier

Init == 
    /\ pc = [i \in ProcSet |-> "a1"]
    /\ barrier = [i \in ProcSet |-> FALSE]

a1(i) == 
    /\ pc[i] = "a1"
    /\ pc' = [pc EXCEPT ![i] = "a2"]
    /\ barrier' = [barrier EXCEPT ![i] = TRUE]
    
a2(i) == 
    /\ pc[i] = "a2"
    \* Other process must have made it to its barrier.
    /\ barrier[1-i]
    /\ pc' = [pc EXCEPT ![i] = "a3"]
    /\ UNCHANGED barrier

Next == 
    \E i \in ProcSet:
        \/ a1(i)
        \/ a2(i)

\* If some process has made it to a3, the other process must already be
\* at a2 or a3.
Inv == \A i \in ProcSet : pc[i] = "a3" => pc[1-i] \in {"a2","a3"}

TypeOK == 
    /\ pc \in [ProcSet -> {"a1","a2","a3"}]
    /\ barrier \in [ProcSet -> BOOLEAN]

IInv == 
    /\ TypeOK
    /\ Inv
    \* Strengthening assertion to make inductive.
    /\ \A i \in ProcSet : 
        /\ pc[i] = "a1" => ~barrier[i]
        /\ pc[i] \in {"a2","a3"} => barrier[i]


====