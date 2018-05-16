--------------------------- MODULE InternalMemory ---------------------------
EXTENDS MemoryInterface
VARIABLES mem, ctl, buf
-----------------------------------------------------------------------------

IInit == (** The initial predicate **)
          (** Initial memory locations have any values in Val **)
        /\ mem \in [Adr -> Val]
          (** Each processor is ready to issue request **)
        /\ ctl = [p \in Proc |-> "rdy"]
          (** each buf[p] is arbitirarily initialized to NoVal **)
        /\ buf = [p \in Proc |-> NoVal]
          (** and memInt is any element of initMemInt **)
        /\ memInt \in InitMemInt

TypeInvariant == (** The type correctness invariant **)
            (** mem is a function from Adr to Val **)
        /\ mem \in [Adr -> Val]
            (** ctl[p] equals "rdy", "busy" or "done" **)
        /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
            (** buf[p] is a request or response **)
        /\ buf \in [Proc -> MReq \/ Val \/ {NoVal}]

(** Processor p issues a request **)
Req(p) ==
        (** Enabled if p is ready to issue a request **)
    /\ ctl[p] = "rdy"
        (** For some req **)
    /\ \E req \in MReq :
            /\ Send(p, req, memInt, memInt')
            /\ buf' = [buf EXCEPT ![p] = req]
            /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(** Perform's p request to memory **)
Do(p) ==
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
                THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                ELSE mem
    /\ buf' = [buf EXCEPT
                    ![p] = IF buf[p].op = "Wr"
                                THEN NoVal
                                ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

(** Return the response to p's request **)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)
ISpec == IInit /\ [][INext]_<<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
THEOREM ISpec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Thu May 17 03:48:38 IST 2018 by ridhm
\* Created Thu May 17 03:27:01 IST 2018 by ridhm
