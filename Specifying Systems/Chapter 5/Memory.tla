------------------------------- MODULE Memory -------------------------------
EXTENDS MemoryInterface
Inner(mem, ctl, buf) == INSTANCE InternalMemory

Spec == \E mem, ctl, buf : Inner(mem, ctl, buf)!ISpec
=============================================================================
\* Modification History
\* Last modified Thu May 17 03:51:54 IST 2018 by ridhm
\* Created Thu May 17 03:50:47 IST 2018 by ridhm
