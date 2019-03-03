----------------------------- MODULE P2TCommit ------------------------------
EXTENDS TLAPS
CONSTANT RM       \* The set of participating resource managers

(***************************************************************************
The following is a specification of transaction commit that is written
in what is perhaps a more natural PlusCal style than that in module
PTCommit because processes "terminate" rather than "deadlocking".  It
is identical to the algorithm in that module except for two changes:

1. The predicate of the `while' loop has been changed so an RM exists
the loop when it terminates.

2. The RManager process is made a `fair' process, meaning that weak
fairness of is assumed.  Weak fairness means that each RM that is
continuously able to take a step must eventually do so.

 `.
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"] ;
  define {
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
    notCommitted == \A rm \in RM : rmState[rm] # "committed" 
   }
  macro Prepare(p) {
    when rmState[p] = "working";
    rmState[p] := "prepared" ;    
   }
   
  macro Decide(p) {
    either { when /\ rmState[p] = "prepared" 
                  /\ canCommit ;
             rmState[p] := "committed"
           }
    or     { when /\ rmState[p] \in {"working", "prepared"}
                  /\ notCommitted ;
             rmState[p] := "aborted"
           }  
   }
   
  fair process (RManager \in RM) {
    start: while (rmState[self] \in {"working", "prepared"}) { 
      either Prepare(self) or Decide(self) }
   }
}
 .'
 
Below is the algorithm's translation.  The translation defines
Termination to be the temporal formula asserting that eventually
all processes terminate.
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, pc

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
notCommitted == \A rm \in RM : rmState[rm] # "committed"


vars == << rmState, pc >>

ProcSet == (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "start"]

start(self) == /\ pc[self] = "start"
               /\ IF rmState[self] \in {"working", "prepared"}
                     THEN /\ \/ /\ rmState[self] = "working"
                                /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             \/ /\ \/ /\ /\ rmState[self] = "prepared"
                                         /\ canCommit
                                      /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                   \/ /\ /\ rmState[self] \in {"working", "prepared"}
                                         /\ notCommitted
                                      /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                          /\ pc' = [pc EXCEPT ![self] = "start"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED rmState

RManager(self) == start(self)

Next == (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* The invariants:                                                         *)
(***************************************************************************)
TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ pc \in [RM -> {"start", "Done"}]

Consistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"
                         
THEOREM Spec => [](TypeOK /\ Consistent)

(***************************************************************************)
(* The following theorem asserts that every execution of the algorithm     *)
(* terminates.                                                             *)
(***************************************************************************)
THEOREM Spec => Termination

(***************************************************************************)
(* TLC checks these two theorems in seconds for a model with 3 RMs.        *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Oct 11 08:14:15 PDT 2011 by lamport
\* Created Mon Oct 10 05:31:02 PDT 2011 by lamport
