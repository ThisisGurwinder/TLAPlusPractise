----------------------------- MODULE BinaryTree -----------------------------

EXTENDS Naturals, FiniteSets, TLC
CONSTANT Val
VARIABLES nodes, parent, left, right

BinaryTree == INSTANCE Tree
NoVal == BinaryTree!NoVal

MaxTwoChildren == \A n \in nodes :
    Cardinality({x \in DOMAIN parent : n=parent[x]}) \leq 2

TypeInvariant == /\ BinaryTree!TypeInvariant
                 /\ MaxTwoChildren
 
NoCycles == BinaryTree!NoCycles
SingleRoot == BinaryTree!SingleRoot

AddRoot(v) == /\ nodes = {}
              /\ nodes' = {v}
              /\ parent' = (v :> NoVal)
              /\ UNCHANGED <<left, right>>
  
InsertLeft(v) == /\ v \notin nodes
                 /\ \E p \in nodes : \neg \E x \in left : parent[x] = p
                 /\ nodes' = nodes \union {v}
                 /\ left' = left \union {v}
                 /\ LET p == CHOOSE p \in nodes : \neg \E x \in left : parent[x] = p
                        IN parent' = parent @@ (v :> p)
                 /\ UNCHANGED right
                 
InsertRight(v) == /\ v \notin nodes
                  /\ \E p \in nodes : \neg \E x \in right : parent[x] = p
                  /\ nodes' = nodes \union {v}
                  /\ left' = left \union {v}
                  /\ LET p == CHOOSE p \in nodes : \neg \E x \in right : parent[x] = p
                        IN parent' = parent @@ (v :> p)
                  /\ UNCHANGED left
  
FullTree == /\ nodes = Val
            /\ UNCHANGED<<nodes, parent, left, right>>
            
Insert(v) == AddRoot(v) \/ InsertLeft(v) \/ InsertRight(v) \/ FullTree

Init == /\ BinaryTree!Init
        /\ left = {}
        /\ right = {}

Next == \E v \in Val: Insert(v)
Spec == Init /\ [][Next]_<<nodes, parent, left, right>>

=============================================================================
\* Modification History
\* Last modified Thu Apr 26 07:41:54 IST 2018 by Gurwinder
\* Created Thu Apr 26 07:30:38 IST 2018 by Gurwinder
