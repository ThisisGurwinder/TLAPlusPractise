------------------------ MODULE SimpleSpannningTree ------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val
VARIABLES nodes, parent

NoVal == CHOOSE v: v \notin Val

TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]
               
PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE) 
 
Init == /\ nodes = {}
        /\ parent = <<>>
        
Insert(v) == /\ v \notin nodes
             /\ nodes' = nodes \union {v}
             /\ parent' = parent @@ (v :> IF nodes = {}
                                                THEN NoVal
                                                ELSE CHOOSE p \in nodes : TRUE)
AddRoot(v) == /\ v \notin nodes
              /\ nodes' = nodes \union {v}
              /\ parent' = parent @@ (v :> NoVal)

FullTree == /\ nodes = Val
            /\ PrintVal("Nodes && Parent : ",
                  <<nodes, parent>>)
            /\ UNCHANGED<<nodes, parent>>  
  
Next == \E v \in Val : Insert(v) \/ FullTree
Spec == Init /\ [][Next]_<<nodes, parent>>

-----------------------------------------------------------------------------
\*THEOREM Spec => [](TypeInvariant)
=============================================================================
\* Modification History
\* Last modified Wed May 16 05:15:55 IST 2018 by ridhm
\* Created Wed May 16 04:53:43 IST 2018 by ridhm
