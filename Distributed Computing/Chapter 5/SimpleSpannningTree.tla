------------------------ MODULE SimpleSpannningTree ------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val
VARIABLES nodes, parent, left, right

NoVal == CHOOSE v: v \notin Val

TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]
               
PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE) 
 
Init == /\ nodes = {}
        /\ parent = <<>>
        /\ left = {}
        /\ right = {}
        
Insert(v) == /\ v \notin nodes
             /\ nodes' = nodes \union {v}
             /\ parent' = parent @@ (v :> IF nodes = {}
                                                THEN NoVal
                                                ELSE CHOOSE p \in nodes : TRUE)
                                                
AddRoot(v) == /\ nodes = {}
              /\ nodes' = {v}
              /\ parent' = parent @@ (v :> NoVal)
              /\ UNCHANGED <<left, right>>
  
InsertLeft(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neq \E x \in left : parent[x] = p
                 /\ nodes' = nodes \union {v}
                 /\ left' = left \union {v}
                 /\ LET p == CHOOSE p \in nodes : \neq \E x \in left : parent[x] = p
                    IN parent' = parent @@ (v :> p)
                 /\ UNCHANGED right


FullTree == /\ nodes = Val
            /\ UNCHANGED<<nodes, parent, left, right>>  
  
Next == \E v \in Val : Insert(v) \/ FullTree
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

-----------------------------------------------------------------------------
\*THEOREM Spec => [](TypeInvariant)
=============================================================================
\* Modification History
\* Last modified Wed May 16 05:23:22 IST 2018 by ridhm
\* Created Wed May 16 04:53:43 IST 2018 by ridhm
