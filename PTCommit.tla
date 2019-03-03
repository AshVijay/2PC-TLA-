------------------------------ MODULE PTCommit ------------------------------
(***************************************************************************)
(* The following EXTENDS statement imports the standard module TLAPS,      *)
(* which defines some operators used for writing proofs.                   *)
(***************************************************************************)
EXTENDS TLAPS
CONSTANT RM       \* The set of participating resource managers

(***************************************************************************
The following PlusCal algorithm is the specification of transaction
commitment.  It was chosen so its translation (the TLA+ formula Spec)
would be equivalent to the specification TCSpec of module TCSpec.

The algorithm uses the single variable rmState, where rmState[rm] is
the state of Resource Manager rm, which is either "working",
"prepared", "committed", or "aborted".  An RM's initial state is
"working".

Mimicking the specification in module TCommit, the operations
Prepare(p) (prepare to commit) and Decide(p) (decide to commit or
abort) are described with macros.  The state predicates canCommit and
notCommitted are defined the same as in TCommit.

The PlusCal `when' statement introduces an enabling condition--a
condition that must hold for execution to proceed past the statement.

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
   
  process (RManager \in RM) {
    start: while (TRUE) { either Prepare(self) or Decide(self) }
   }
}
 .'
 
The  while (TRUE)   loop in the RM's code means that it terminates
only by deadlocking.  There is no fundamental difference between
termination and deadlock.  Termination is simply deadlock that we want
to happen.  The distinction between termination and deadlock can be
made only when an algorithm is described in some particular constrained
fashion.  This is the case for algorithms described in PlusCal, where
termination means that control in every process is at the end of the
process's code.  Since TLA+ has no built-in notion of process or
control, the distinction does not exist in a specification written in
TLA+.  One could introduce a particular variable whose value indicates
whether or not processes should be considered to have terminated.
However, that would produce a more complicated and less elegant
specification than the one in module TCommit that we are reproducing
here.  A PlusCal specification of transaction commit in which processes
terminate the way we expect them to is given in module P2TCommit.
 
The following is the TLA+ translation of the algorithm, inserted
automatically by the translator.  Comparing it to the specification in
module TCommit, we see that when the definitions are completely
expanded, formulas Spec and TCSpec are identical except for a few
insignificant differences--mainly because Spec has some one-element
conjunction lists of the form /\ P where TCSpec has just the formula P.
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE rmState

(* define statement *)
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
notCommitted == \A rm \in RM : rmState[rm] # "committed"


vars == << rmState >>

ProcSet == (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]

RManager(self) == \/ /\ rmState[self] = "working"
                     /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                  \/ /\ \/ /\ /\ rmState[self] = "prepared"
                              /\ canCommit
                           /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                        \/ /\ /\ rmState[self] \in {"working", "prepared"}
                              /\ notCommitted
                           /\ rmState' = [rmState EXCEPT ![self] = "aborted"]


Next == (\E self \in RM: RManager(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************)
(* The following INSTANCE statement imports into the current module every  *)
(* defined formula F of module TCSpec, renamed to TC!F.  (More precisely,  *)
(* formula TC!F of this module is formula F with the parameters RM and     *)
(* rmState of module TCSpec replaced by the parameters with the same name  *)
(* of this module.                                                         *)
(***************************************************************************)
TC == INSTANCE TCommit

(***************************************************************************)
(* The following theorem checks that Spec and the imported specification   *)
(* TC!TCSpec are equivalent.  Since TLAPS does not yet support temporal    *)
(* logic reasoning, proofs of statements that assert a temporal formula    *)
(* are omitted.  For invariance and refinement properties the, required    *)
(* temporal reasoning is trivial.  (This theorem essentially asserts that  *)
(* the two specifications refine each other.)                              *)
(***************************************************************************)
THEOREM Spec <=> TC!TCSpec
  <1>1. Init <=> TC!TCInit
    BY DEF Init, TC!TCInit
  <1>2. [Next]_rmState <=> [TC!TCNext]_rmState
    BY DEF Next, ProcSet, RManager, canCommit, notCommitted, 
           TC!TCNext, TC!Prepare, TC!Decide, TC!canCommit, TC!notCommitted
  <1>3. QED
    (***********************************************************************)
    (* Follows from <1>1 and <1>2 and the definitions of Spec and          *)
    (* TC!TCSpec by trivial temporal logic.                                *)
    (***********************************************************************)
    PROOF OMITTED

(***************************************************************************)
(* We now assert invariance properties of the specification.               *)
(***************************************************************************)
TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Consistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

(***************************************************************************)
(* The following theorem asserts that TypeOK and Consistent are invariants *)
(* of the protocol.  In the proof, SMT is defined in the imported module   *)
(* TLAPS so that using it invokes a default SMT solver as the backend      *)
(* prover.  These proofs were done with the Toolbox configured to use CVC3 *)
(* as the default SMT solver.                                              *)
(***************************************************************************)
THEOREM Spec => [](TypeOK /\ Consistent)
<1>1. Init => TypeOK /\ Consistent
  BY SMT DEF Init, TypeOK, Consistent
<1>2. (TypeOK /\ Consistent) /\ [Next]_vars => (TypeOK /\ Consistent)'
  BY SMT DEF TypeOK, Consistent, Next, vars, RManager, canCommit, notCommitted
<1>3. QED
  PROOF OMITTED
  (*************************************************************************)
  (* Follows immediately from <1>1, <1>2, the definition of Spec, the TLA  *)
  (* proof rule                                                            *)
  (*                                                                       *)
  (*       P /\ [N]_v => P'                                                *)
  (*     --------------------                                              *)
  (*     P /\ [][N]_v => []P                                               *)
  (*                                                                       *)
  (* and simple logic.                                                     *)
  (*************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Oct 11 08:15:04 PDT 2011 by lamport
\* Created Mon Oct 10 05:31:02 PDT 2011 by lamport
