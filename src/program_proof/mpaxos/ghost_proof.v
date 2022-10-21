From Perennial.program_proof Require Import grove_prelude.
(* From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb. *)
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list csum.
From Perennial.Helpers Require Import ListSolver.

Section mpaxos_protocol.

Context `{!heapGS Σ}.

Record mp_system_names :=
{
  mp_proposal_gn : gname ;
  mp_state_gn : gname ;
}.

Record mp_server_names :=
{
  mp_urpc_gn : urpc_proof.server_chan_gnames ;
  mp_accepted_gn : gname ;
  mp_vote_gn : gname ; (* token for granting vote to a node in a particular epoch *)
}.

Context `{EntryType:Type}.

Local Definition logR := mono_listR (leibnizO EntryType).

Context (config: list mp_server_names).

Class mp_ghostG Σ := {
    mp_ghost_epochG :> mono_natG Σ ;
    mp_ghost_proposalG :> inG Σ (gmapR (u64) (csumR (exclR unitO) logR)) ;
    mp_ghost_acceptedG :> inG Σ (gmapR (u64) logR) ;
    mp_ghost_commitG :> inG Σ logR ;
    mp_proposal_escrowG :> inG Σ (gmapR (u64) (dfrac_agreeR unitO)) ;
}.

Context `{!mp_ghostG Σ}.

Implicit Type γsrv : mp_server_names.
Implicit Type γsys : mp_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_proposal_unused γsys epoch : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinl (Excl ()) ]}.
Definition own_proposal γsys epoch σ : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinr (●ML (σ : list (leibnizO (EntryType))))]}.
Definition is_proposal_lb γsys epoch σ : iProp Σ :=
  own γsys.(mp_proposal_gn) {[ epoch := Cinr (◯ML (σ : list (leibnizO (EntryType))))]}.

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

Definition own_vote_tok γsrv epoch : iProp Σ :=
  own γsrv.(mp_vote_gn) {[ epoch := to_dfrac_agree (DfracOwn 1) ()]}.

Definition own_accepted γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ●ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_lb γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ◯ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_ro γ epoch σ : iProp Σ :=
  own γ.(mp_accepted_gn) {[ epoch := ●ML□ (σ : list (leibnizO (EntryType)))]}.

(* TODO: if desired, can make these exclusive by adding an exclusive token to each *)
Definition own_ghost γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition own_commit γ σ : iProp Σ :=
  own γ.(mp_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition is_ghost_lb γ σ : iProp Σ :=
  own γ.(mp_state_gn) (◯ML (σ : list (leibnizO (EntryType)))).

(* FIXME: this definition needs to only require a quorum *)
Definition committed_by epoch σ : iProp Σ :=
  ∀ γsrv, ⌜γsrv ∈ config⌝ → is_accepted_lb γsrv epoch σ.

Definition old_proposal_max γsys epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜int.nat epoch_old < int.nat epoch⌝ →
   committed_by epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition mpN := nroot .@ "mp".
Definition ghostN := mpN .@ "ghost".

Definition sysN := ghostN .@ "sys".
Definition opN := ghostN .@ "op".

(* XXX(namespaces):
   The update for the ghost state is fired while the sys_inv is open.
   Additionally, the update is fired while the is_valid_inv is open, so we need
   the initial mask to exclude those invariants.
*)
Definition is_valid_inv γsys σ op : iProp Σ :=
  inv opN (
    £ 1 ∗
    (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_ghost γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γsys (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True)) ∨
    is_ghost_lb γsys (σ ++ [op])
  )
.

Definition is_proposal_valid γ σ : iProp Σ :=
  □(∀ σ', ⌜σ' ⪯ σ⌝ → own_commit γ σ' ={⊤∖↑sysN}=∗ own_commit γ σ).

Definition is_proposal_facts γ epoch σ: iProp Σ :=
  old_proposal_max γ epoch σ ∗
  is_proposal_valid γ σ.

(* FIXME: these definitions need to change *)
Definition own_escrow_toks γsrv epoch : iProp Σ :=
  [∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch' ≤ int.nat epoch⌝ ∨ own_vote_tok γsrv epoch'
.

Record MPaxosState :=
  mkMPaxosState
    {
      mp_epoch:u64 ;
      mp_acceptedEpoch:u64 ;
      mp_log:list EntryType ;
    }.

Definition own_replica_ghost γsys γsrv (st:MPaxosState) : iProp Σ.
Admitted.

Definition own_leader_ghost γsys (st:MPaxosState): iProp Σ.
Admitted.

Lemma ghost_leader_propose γsys st entry :
  own_leader_ghost γsys st -∗
  £ 1 -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_ghost γsys someσ ∗
      (⌜someσ = st.(mp_log)⌝ -∗ own_ghost γsys (someσ ++ [entry]) ={∅,⊤∖↑ghostN}=∗ True))
  ={⊤}=∗
  own_leader_ghost γsys (mkMPaxosState st.(mp_epoch) st.(mp_acceptedEpoch) (st.(mp_log) ++ [entry]))∗
  is_proposal_lb γsys st.(mp_epoch) (st.(mp_log) ++ [entry]) ∗
  is_proposal_facts γsys st.(mp_epoch) (st.(mp_log) ++ [entry])
.
Proof.
Admitted.

Lemma ghost_replica_get_lb γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  is_accepted_lb γsrv st.(mp_acceptedEpoch) st.(mp_log).
Proof.
Admitted.

Lemma ghost_replica_accept_same_epoch γsys γsrv st epoch' log' :
  int.nat st.(mp_epoch) ≤ int.nat epoch' →
  int.nat st.(mp_acceptedEpoch) = int.nat epoch' →
  length st.(mp_log) ≤ length log' →
  own_replica_ghost γsys γsrv st -∗
  is_proposal_lb γsys epoch' log' -∗
  is_proposal_facts γsys epoch' log'
  ==∗
  ⌜st.(mp_epoch) = epoch'⌝ ∗
  own_replica_ghost γsys γsrv (mkMPaxosState epoch' epoch' log').
Proof.
Admitted.

Lemma ghost_replica_accept_same_epoch_old γsys γsrv st epoch' log' :
  int.nat st.(mp_epoch) ≤ int.nat epoch' →
  int.nat st.(mp_acceptedEpoch) = int.nat epoch' →
  length log' ≤ length st.(mp_log) →
  own_replica_ghost γsys γsrv st -∗
  is_proposal_lb γsys epoch' log' -∗
  is_accepted_lb γsrv epoch' log'.
Proof.
Admitted.

Lemma ghost_replica_accept_new_epoch γsys γsrv st epoch' log' :
  int.nat st.(mp_epoch) ≤ int.nat epoch' →
  int.nat st.(mp_acceptedEpoch) ≠ int.nat epoch' →
  own_replica_ghost γsys γsrv st -∗
  is_proposal_lb γsys epoch' log' -∗
  is_proposal_facts γsys epoch' log'
  ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState epoch' epoch' log').
Proof.
Admitted.

(* TODO: this is probably just the definition *)
Lemma establish_committed_by epoch σ (W:gset nat) :
  (∀ s, s ∈ W → s < length config) →
  2 * (size W) > length config →
  ([∗ list] s0↦γsrv' ∈ config, ⌜s0 ∈ W⌝ → is_accepted_lb γsrv' epoch σ) -∗
  committed_by epoch σ.
Proof.
Admitted.

Definition sys_inv γsys := inv sysN
(
  ∃ σ epoch,
  own_commit γsys σ ∗
  committed_by epoch σ ∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ
).

Lemma ghost_commit γsys epoch σ :
  sys_inv γsys -∗
  committed_by epoch σ -∗
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ
  ={⊤}=∗ (* XXX: this is ⊤ because the user-provided fupd is fired, and it is allowed to know about ⊤ *)
  is_ghost_lb γsys σ.
Proof.
Admitted.


Definition is_accepted_upper_bound γsrv log (acceptedEpoch newEpoch:u64) : iProp Σ :=
  ∃ logPrefix,
  ⌜logPrefix ⪯ log⌝ ∗
  is_accepted_ro γsrv acceptedEpoch logPrefix ∗
  □ (∀ epoch', ⌜int.nat acceptedEpoch < int.nat epoch'⌝ -∗
            ⌜int.nat epoch' < int.nat newEpoch⌝ -∗
            is_accepted_ro γsrv epoch' [])
.

Lemma is_accepted_upper_bound_mono_epoch γsrv log acceptedEpoch acceptedEpoch' newEpoch :
  int.nat acceptedEpoch < int.nat acceptedEpoch' →
  int.nat acceptedEpoch' < int.nat newEpoch →
  is_accepted_upper_bound γsrv log acceptedEpoch newEpoch -∗
  is_accepted_upper_bound γsrv [] acceptedEpoch' newEpoch
.
Proof.
  intros Hineq Hineq2.
  iIntros "#Hub".
  iExists [].
  iSplitL; first done.
  iSplit.
  {
    iDestruct "Hub" as (?) "(_ & _ & #Hwand)".
    iApply "Hwand".
    { done. }
    { done. }
  }
  {
    iModIntro.
    iIntros.
    iDestruct "Hub" as (?) "(_ & _ & #Hwand)".
    iApply "Hwand".
    { iPureIntro.
      word. }
    { iPureIntro.
      word. }
  }
Qed.

Lemma is_accepted_upper_bound_mono_log γsrv log log' acceptedEpoch newEpoch :
  prefix log log' →
  is_accepted_upper_bound γsrv log acceptedEpoch newEpoch -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch
.
Proof.
Admitted.

Lemma is_proposal_lb_compare γsys log log' epoch :
  length log' ≤ length log →
  is_proposal_lb γsys epoch log -∗
  is_proposal_lb γsys epoch log' -∗
  ⌜prefix log' log⌝
.
Proof.
Admitted.

Lemma become_leader γsys (W:gset nat) latestLog acceptedEpoch newEpoch:
  2 * (size W) > length config →
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → is_accepted_upper_bound γsrv latestLog acceptedEpoch newEpoch) -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv newEpoch) ={↑sysN}=∗
  own_leader_ghost γsys (mkMPaxosState newEpoch newEpoch latestLog)
.
Proof.
Admitted.


Lemma ghost_leader_get_proposal γsys st :
  own_leader_ghost γsys st -∗
  is_proposal_lb γsys st.(mp_epoch) st.(mp_log) ∗
  is_proposal_facts γsys st.(mp_epoch) st.(mp_log)
.
Proof.
Admitted.

Lemma ghost_replica_helper1 γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  ⌜int.nat st.(mp_acceptedEpoch) < int.nat st.(mp_epoch)⌝.
Proof.
Admitted.

Lemma ghost_replica_enter_new_epoch γsys γsrv st newEpoch :
  int.nat newEpoch > int.nat st.(mp_epoch) →
  own_replica_ghost γsys γsrv st ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState newEpoch st.(mp_acceptedEpoch) st.(mp_log)) ∗
  own_vote_tok γsrv newEpoch ∗
  is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) newEpoch ∗
  is_proposal_lb γsys st.(mp_acceptedEpoch) st.(mp_log) ∗
  is_proposal_facts γsys st.(mp_acceptedEpoch) st.(mp_log)
.
Proof.
Admitted.

End mpaxos_protocol.
