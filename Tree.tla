-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Val \* Set of values node can take
VARIABLES nodes, parent \* Sets of nodes, functions that takes nodes to parent

NoVal == CHOOSE v: v \notin Val \* Root parent is no val

TypeInvariant == /\ nodes \subseteq Val
                 /\ parent \in [nodes -> nodes \union {NoVal}]
 
 (** Transitive Closure, taken from lamports hyperbook **)
 
R**S == LET T == {rs \in R \times S : rs[1][2] = rs[2][1]}
            IN {<<x[1][1], x[2][2]>> : x \in T}

NodesOf(R) == { r[1] : r \in R} \union { r[2] : r \in R }

SimpleTC(R) ==
    LET RECURSIVE STC(_)
        STC(n) == IF n=1 THEN R
                            ELSE STC(n-1) \union STC(n-1)**R
    IN IF R = {} THEN {} ELSE STC(Cardinality(NodesOf(R))+1)  \* We add 1 to catch cycles

(** Convert a function to relation **)
Relation(f) == {<<x, f[x]>> : x \in DOMAIN f }

(** Transitive Closure, taking a function as an argument **)
TC(f) == SimpleTC(Relation(f))

NoCycles == \lnot \E n \in nodes : <<n,n>> \in TC(parent)
SingleRoot == \/ nodes = {}
              \/ \E root \in nodes : \A n \in nodes \ {root} :
                    <<n, root>> \in TC(parent)

Init == /\ nodes = {}
        /\ parent = <<>>
Insert(v) == /\ v \notin nodes
             /\ nodes' = nodes \union {v}
             /\ parent' = parent @@ ( v :> IF nodes = {}
                                                THEN NoVal
                                                ELSE CHOOSE p \in nodes : TRUE )
AddCycle == /\ Cardinality(nodes)>1
            /\ LET x == CHOOSE x \in nodes : parent[x] /= NoVal
                IN parent' = [parent EXCEPT ![x] = CHOOSE y \in nodes : TRUE]
            /\ UNCHANGED nodes
AddRoot(v) == /\ v \notin nodes
              /\ nodes' = nodes \union {v}
              /\ parent' = parent @@ (v :> NoVal)
  
Next == \/ \E v \in Val : Insert(v)
Spec == Init \/ [][Next]_<<nodes, parent>>

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant \/ NoCycles \/ SingleRoot)
=============================================================================
\* Modification History
\* Last modified Thu Apr 26 08:07:49 IST 2018 by Gurwinder
\* Created Thu Apr 26 07:43:22 IST 2018 by Gurwinder
