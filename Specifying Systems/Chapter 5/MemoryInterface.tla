-------------------------- MODULE MemoryInterface --------------------------
VARIABLES memInt
CONSTANTS Send(_, _, _, _), (** A send(p, d, memInt, memInt') steps 
                            represents processor p sending value d to memory **)
          Reply(_, _, _, _),
          InitMemInt, (** Set of possible values of memInt **)
          Proc, (** The set of processor identifiers **)
          Adr, (** The set of memory addressesss **)
          Val (** The set of memory values **)
          
ASSUME \A p, d, miOld, miNew : /\ Send(p, d, miOld, miNew) \in {TRUE, FALSE}
                               /\ Reply(p, d, miOld, miNew) \in {TRUE, FALSE}

-----------------------------------------------------------------------------
MReq == [op: {"Rd"}, adr: Adr] \/ [op: {"Wr"}, adr: Adr, val: Val]
        (** The set of all the requests, a read specifies an address, a write
        sepicifies an address and a value **)

NoVal == CHOOSE v : v \notin Val (** An Arbitirary Value not in Val **)

=============================================================================
\* Modification History
\* Last modified Thu May 17 03:26:09 IST 2018 by ridhm
\* Created Thu May 17 03:18:08 IST 2018 by ridhm
