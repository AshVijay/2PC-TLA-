---------------------------- MODULE P2TwoPhase -----------------------------
(****************************************************************************
This specification is a more "realistic" description of the Two-Phase
commit protocol, meaning that it is a bit closer to an actual
implementation than the specification in module PTwoPhase.  It also has
fair processes, so it refines the specification in module P2TCommit.

The PlusCal algorithm differs from that in module PTwoPhase in the
following ways:

- The processes terminate in the expected way, by exiting from their
while loops.

- The tmState variable has a single "decided" value, indicating that it
has either committed or aborted.

- Instead of sending a single "Commit" or "Abort" message that is read
by all RMs, the TM sends a separate message to each RM.  The TM sends
each message in a separate atomic action, the order in which the
messages are sent being nondeterministically chosen.  To implement this
finer grain of atomicity, the TM maintains a local variable unSent that
is the set of RMs to which it has not yet sent a "Commit" or "Abort"
message.  Note that in PlusCal, an atomic action is the execution of a
process's code from one label to the next.

- `fair process' instead of `process' statements are used, so the
specification asserts weak fairness of each process.
****************************************************************************)
CONSTANT RM \* The set of resource managers

TM == CHOOSE tm : tm \notin RM  \* The transaction manager

(***************************************************************************
 `.
--algorithm TwoPhaseCommit {
  variables rmState = [rm \in RM |-> "working"], 
            tmState = "init",
            tmPrepared   = {},
            msgs = {} ;     

  macro SendMsg(m) { msgs := msgs \cup {m} } 
  macro RcvMsg(m) { await m \in msgs }

  macro TMRcvPrepared() {
    (***********************************************************************)
    (* The TM receives a "Prepared" message from some resource manager.    *)
    (***********************************************************************)
    with (rm \in RM) { 
      RcvMsg([type |-> "Prepared", rm |-> rm]);
      tmPrepared := tmPrepared \cup {rm}
     }
   }
  macro TMDecideCommit() {
    (***********************************************************************)
    (* The TM commits the transaction; enabled iff the TM is in its        *)
    (* initial state and every RM has sent a "Prepared" message.           *)
    (***********************************************************************)
    await tmPrepared = RM ;
    tmState := "decided" ;
   }
  macro TMDecideAbort() {
    (***********************************************************************)
    (* The TM spontaneously aborts the transaction.                        *)
    (***********************************************************************)
    tmState := "decided" ;
   }
  macro RMPrepare(rm) {
    (***********************************************************************)
    (* Resource manager rm prepares.                                       *)
    (***********************************************************************)
    await rmState[rm] = "working" ;
    rmState[rm] := "prepared" ;
    SendMsg([type |-> "Prepared", rm |-> rm])
   }
  macro RMChooseToAbort(rm) {
    (***********************************************************************)
    (* Resource manager rm spontaneously decides to abort.  As noted       *)
    (* above, rm does not send any message in our simplified spec.         *)
    (***********************************************************************)
    await rmState[rm] = "working" ;
    rmState[rm] := "aborted"
   }
  macro RMRcvCommitMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to commit.                    *)
    (***********************************************************************)
    RcvMsg([type |-> "Commit", rm |-> rm]) ;
    rmState[rm] := "committed" 
   }
  macro RMRcvAbortMsg(rm) {
    (***********************************************************************)
    (* Resource manager rm is told by the TM to abort.                     *)
    (***********************************************************************)
    RcvMsg ([type |-> "Abort", rm |-> rm]) ;
    rmState[rm] := "aborted" 
   }
  fair process (TManager = TM) 
    variable unSent = RM ; {
    tmstart: while (tmState = "init") { 
               either { TMDecideCommit() ;
                        cmting : while (unSent # {}) {
                                   with (rm \in unSent) {
                                     SendMsg([type |-> "Commit", rm |-> rm]);
                                     unSent := unSent \ {rm}
                                    }
                                  }
                      }
               or     { TMDecideAbort() ;
                        abting : while (unSent # {}) {
                                   with (rm \in unSent) {
                                     SendMsg([type |-> "Abort", rm |-> rm]);
                                     unSent := unSent \ {rm}
                                    }
                                 }
                      } 
               or    TMRcvPrepared()
              }
   }
  fair process (RManager \in RM) {
    rmstart: while (rmState[self] \in {"working", "prepared"}) {
               either RMPrepare(self) or RMChooseToAbort(self) 
                 or RMRcvCommitMsg(self) or RMRcvAbortMsg(self)
              }
   }
}
 .'
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, tmPrepared, msgs, pc, unSent

vars == << rmState, tmState, tmPrepared, msgs, pc, unSent >>

ProcSet == {TM} \cup (RM)

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ tmPrepared = {}
        /\ msgs = {}
        (* Process TManager *)
        /\ unSent = RM
        /\ pc = [self \in ProcSet |-> CASE self = TM -> "tmstart"
                                        [] self \in RM -> "rmstart"]

tmstart == /\ pc[TM] = "tmstart"
           /\ IF tmState = "init"
                 THEN /\ \/ /\ tmPrepared = RM
                            /\ tmState' = "decided"
                            /\ pc' = [pc EXCEPT ![TM] = "cmting"]
                            /\ UNCHANGED tmPrepared
                         \/ /\ tmState' = "decided"
                            /\ pc' = [pc EXCEPT ![TM] = "abting"]
                            /\ UNCHANGED tmPrepared
                         \/ /\ \E rm \in RM:
                                 /\ ([type |-> "Prepared", rm |-> rm]) \in msgs
                                 /\ tmPrepared' = (tmPrepared \cup {rm})
                            /\ pc' = [pc EXCEPT ![TM] = "tmstart"]
                            /\ UNCHANGED tmState
                 ELSE /\ pc' = [pc EXCEPT ![TM] = "Done"]
                      /\ UNCHANGED << tmState, tmPrepared >>
           /\ UNCHANGED << rmState, msgs, unSent >>

cmting == /\ pc[TM] = "cmting"
          /\ IF unSent # {}
                THEN /\ \E rm \in unSent:
                          /\ msgs' = (msgs \cup {([type |-> "Commit", rm |-> rm])})
                          /\ unSent' = unSent \ {rm}
                     /\ pc' = [pc EXCEPT ![TM] = "cmting"]
                ELSE /\ pc' = [pc EXCEPT ![TM] = "tmstart"]
                     /\ UNCHANGED << msgs, unSent >>
          /\ UNCHANGED << rmState, tmState, tmPrepared >>

abting == /\ pc[TM] = "abting"
          /\ IF unSent # {}
                THEN /\ \E rm \in unSent:
                          /\ msgs' = (msgs \cup {([type |-> "Abort", rm |-> rm])})
                          /\ unSent' = unSent \ {rm}
                     /\ pc' = [pc EXCEPT ![TM] = "abting"]
                ELSE /\ pc' = [pc EXCEPT ![TM] = "tmstart"]
                     /\ UNCHANGED << msgs, unSent >>
          /\ UNCHANGED << rmState, tmState, tmPrepared >>

TManager == tmstart \/ cmting \/ abting

rmstart(self) == /\ pc[self] = "rmstart"
                 /\ IF rmState[self] \in {"working", "prepared"}
                       THEN /\ \/ /\ rmState[self] = "working"
                                  /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                                  /\ msgs' = (msgs \cup {([type |-> "Prepared", rm |-> self])})
                               \/ /\ rmState[self] = "working"
                                  /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                  /\ msgs' = msgs
                               \/ /\ ([type |-> "Commit", rm |-> self]) \in msgs
                                  /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                  /\ msgs' = msgs
                               \/ /\ ([type |-> "Abort", rm |-> self]) \in msgs
                                  /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                  /\ msgs' = msgs
                            /\ pc' = [pc EXCEPT ![self] = "rmstart"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                            /\ UNCHANGED << rmState, msgs >>
                 /\ UNCHANGED << tmState, tmPrepared, unSent >>

RManager(self) == rmstart(self)

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(TManager)
        /\ \A self \in RM : WF_vars(RManager(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Message ==
  (*************************************************************************)
  (* The set of all possible messages.  For messages of type "Prepared",   *)
  (* the message's rm indicates the sender; for messages of type "Commit"  *)
  (* and "Abort", it indicates the receiver.                               *)
  (*************************************************************************)
  [type : {"Prepared", "Commit", "Abort"}, rm: RM]
  
TypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant.  TLC checks the invariance of TypeOK  *)
  (* in a few seconds for a model with 3 RMs.                              *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "decided"}
  /\ tmPrepared \subseteq RM
  /\ msgs  \subseteq Message
  /\ pc \in { p \in [ProcSet -> {"tmstart", "rmstart", "cmting", "abting", "Done"}] : 
               \A self \in ProcSet : 
                  p[self] \in CASE self = TM   -> {"tmstart", "cmting", "abting", "Done"}
                                [] self \in RM -> {"rmstart", "Done"} }

(***************************************************************************)
(* We now check refinement.  We showed that the algorithm of module        *)
(* PTwoPhase implements that of module PTCommit under the refinement       *)
(* mapping                                                                 *)
(*                                                                         *)
(*   rmState <- rmState                                                    *)
(*                                                                         *)
(* meaning that formula Spec of PTwoPhase implies the formula obtained     *)
(* from formula Spec of PTCommit when the variable rmState of PTwoPhase is *)
(* substituted for the variable rmState of PTCommit.  The refinement       *)
(* mapping under which the specification Spec of this module implements    *)
(* specification Spec of module P2TCommit must specify substitutions for   *)
(* the two variables rmState and pc of module P2TCommit.  The refinement   *)
(* mapping we useis                                                        *)
(*                                                                         *)
(*   rmState <- rmState                                                    *)
(*   pc <- pcBar                                                           *)
(*                                                                         *)
(* where pcBar is the expression defined below.  The INSTANCE statement    *)
(* that follows it defines PTC!Spec to be the formula obtained from        *)
(* formula Spec of P2TCommit by these substitutions (plus the substitution *)
(* RM <- RM).                                                              *)
(***************************************************************************)
pcBar == [i \in RM |-> IF pc[i] = "rmstart" THEN "start" ELSE "Done"]

PTC == INSTANCE P2TCommit WITH pc <- pcBar

(***************************************************************************)
(* The following theorem is the formal assertion that our specification of *)
(* two-phase commit implements the specification of transaction commit in  *)
(* module P2TCommit.  The specifications include fairness assertions, so   *)
(* the theorem asserts that the two-phase commit algorithm implements the  *)
(* fairness requirements of transaction commit.  TLC checks the            *)
(* correctness of this theorem in seconds for a model containing 3 RMs.    *)
(***************************************************************************)
THEOREM Spec => PTC!Spec

=============================================================================
\* Modification History
\* Last modified Wed Oct 12 02:52:12 PDT 2011 by lamport
\* Created Mon Oct 10 06:26:47 PDT 2011 by lamport
