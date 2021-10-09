---- MODULE function ----
EXTENDS TLC
Flags == {"f1", "f2"}
(*--algorithm flags
variables 
    flags = [f \in Flags |-> FALSE];
begin
    with f \in Flags do
        flags[f] := TRUE;
    end with;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f6bd63d6" /\ chksum(tla) = "36713cbd")
VARIABLES flags, pc

vars == << flags, pc >>

Init == (* Global variables *)
        /\ flags = [f \in Flags |-> FALSE]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ \E f \in Flags:
              flags' = [flags EXCEPT ![f] = TRUE]
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

====
