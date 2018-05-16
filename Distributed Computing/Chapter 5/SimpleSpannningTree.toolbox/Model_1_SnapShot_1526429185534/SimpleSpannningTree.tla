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
        
AddRoot(v) == /\ nodes = {}
              /\ nodes' = {v}
              /\ parent' = (v :> NoVal)
              /\ UNCHANGED <<left, right>>
  
InsertLeft(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neg \E x \in left : parent[x]=p
                 /\ nodes' = nodes \union {v}
                 /\ left' = left \union {v}
                 /\ LET p == CHOOSE p \in nodes : \neg \E x \in left : parent[x] = p
                    IN parent' = parent @@ (v :> p)
                 /\ UNCHANGED right

InsertRight(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neg \E x \in right : parent[x]=p
                 /\ nodes' = nodes \union {v}
                 /\ right' = right \union {v}
                 /\ LET pR == CHOOSE pR \in nodes : \neg \E xR \in right : parent[xR] = pR
                    IN parent' = parent @@ (v :> pR)
                 /\ UNCHANGED left
                 
FullTree == /\ nodes = Val
            /\ PrintVal(nodes, parent)
            /\ PrintVal(left, right)
            /\ UNCHANGED<<nodes, parent, left, right>>  

Insert(v) == AddRoot(v) \/ InsertLeft(v) \/ InsertRight(v) \/ FullTree
  
Next == \E v \in Val : Insert(v)
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

-----------------------------------------------------------------------------
\*THEOREM Spec => [](TypeInvariant)
=============================================================================
\* Modification History
\* Last modified Wed May 16 05:36:20 IST 2018 by ridhm
\* Created Wed May 16 04:53:43 IST 2018 by ridhm
