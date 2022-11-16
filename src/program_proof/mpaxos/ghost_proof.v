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

(* This definition needs to only require a quorum *)
Definition committed_by epoch σ : iProp Σ :=
  ∃ (W:gset nat),
  ⌜(∀ s, s ∈ W → s < length config)⌝ ∗
  ⌜2 * (size W) > length config⌝ ∗
  ([∗ list] s0↦γsrv' ∈ config, ⌜s0 ∈ W⌝ → is_accepted_lb γsrv' epoch σ).

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

Record MPaxosState :=
  mkMPaxosState
    {
      mp_epoch:u64 ;
      mp_acceptedEpoch:u64 ;
      mp_log:list EntryType ;
    }.

Definition is_accepted_upper_bound γsrv log (acceptedEpoch newEpoch:u64) : iProp Σ :=
  ∃ logPrefix,
  ⌜logPrefix ⪯ log⌝ ∗
  is_accepted_ro γsrv acceptedEpoch logPrefix ∗
  □ (∀ epoch', ⌜int.nat acceptedEpoch < int.nat epoch'⌝ -∗
            ⌜int.nat epoch' < int.nat newEpoch⌝ -∗
            is_accepted_ro γsrv epoch' [])
.


Definition own_replica_ghost γsys γsrv (st:MPaxosState) : iProp Σ :=
  "#Hprop_lb" ∷ is_proposal_lb γsys st.(mp_acceptedEpoch) st.(mp_log) ∗
  "#Hprop_facts" ∷ is_proposal_facts γsys st.(mp_acceptedEpoch) st.(mp_log) ∗
  "#Hacc_lb" ∷ is_accepted_lb γsrv st.(mp_acceptedEpoch) st.(mp_log) ∗
  "%HepochIneq" ∷ ⌜int.nat st.(mp_acceptedEpoch) ≤ int.nat st.(mp_epoch)⌝ ∗

  "Hacc" ∷ (if (decide (int.nat st.(mp_acceptedEpoch) = int.nat st.(mp_epoch))) then
                  own_accepted γsrv st.(mp_epoch) st.(mp_log)
                else
                 own_accepted γsrv st.(mp_epoch) []) ∗
   (* XXX: could combine this with the previous proposition *)
  "#Hacc_ub" ∷ (⌜int.nat st.(mp_acceptedEpoch) < int.nat st.(mp_epoch)⌝ →
                 is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) st.(mp_epoch)) ∗


  "Hunused" ∷ ([∗ set] e ∈ (fin_to_set u64), (⌜int.nat e > int.nat st.(mp_epoch)⌝ → own_accepted γsrv e [])) ∗
  "Hvotes" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜int.nat epoch' ≤ int.nat st.(mp_epoch)⌝ ∨ own_vote_tok γsrv epoch')
.

Definition own_leader_ghost γsys (st:MPaxosState): iProp Σ :=
  "Hprop" ∷ own_proposal γsys st.(mp_epoch) st.(mp_log) ∗
  "#Hprop_facts" ∷ is_proposal_facts γsys st.(mp_epoch) st.(mp_log)
.

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
  iNamed 1.
  iIntros "Hlc Hupd".

  iMod (own_update with "Hprop") as "Hprop".
  {
    apply singleton_update.
    apply csum_update_r.
    apply mono_list_update.
    instantiate (1:=(st.(mp_log) ++ [entry])).
    apply prefix_app_r.
    done.
  }

  iDestruct (own_mono _ _
               {[ st.(mp_epoch) := Cinr (◯ML _) ]}
              with "Hprop") as "#Hprop_lb".
  {
    apply singleton_mono.
    apply Cinr_included.
    apply mono_list_included.
  }

  iFrame "∗#".

  iAssert (|={⊤}=> is_proposal_facts γsys st.(mp_epoch) (st.(mp_log) ++ [entry]))%I with "[Hupd Hlc]" as ">#Hvalid2".
  {
    iDestruct "Hprop_facts" as "(Hmax & Hvalid)".
    iSplitL "".
    { (* old proposal max *)
      iModIntro.
      unfold old_proposal_max.
      iModIntro.
      iIntros.
      iAssert (⌜σ_old ⪯ st.(mp_log)⌝)%I as "%Hprefix".
      {
        iApply "Hmax".
        {
          done.
        }
        { iFrame "#". }
      }
      iPureIntro.
      apply prefix_app_r.
      done.
    }

    iAssert (|={⊤}=> is_valid_inv γsys st.(mp_log) entry)%I with "[Hupd Hlc]" as ">#Hinv".
    {
      iMod (inv_alloc with "[Hupd Hlc]") as "$".
      {
        iNext.
        iLeft.
        iFrame.
      }
      done.
    }
    (* prove is_proposal_valid γ (σ ++ [op]) *)
    iModIntro.
    iModIntro.
    iIntros (σ') "%Hσ' Hσ'".
    assert (σ' ⪯ st.(mp_log) ∨ σ' = (st.(mp_log) ++ [entry])) as [Hprefix_old|Hlatest].
    { (* TODO: list_solver. *)
      (* TODO: copy/paste from pb_ghost *)
      assert (Hlen := Hσ').
      apply prefix_length in Hlen.
      assert (length σ' = length (st.(mp_log) ++ [entry]) ∨ length σ' < length (st.(mp_log) ++ [entry])) as [|] by word.
      {
        right.
        apply list_prefix_eq; eauto.
        lia.
      }
      {
        left.
        rewrite app_length in H.
        simpl in H.
        apply list_prefix_bounded.
        { word. }
        intros.
        assert (st.(mp_log) !! i = (st.(mp_log) ++ [entry]) !! i).
        {
          rewrite lookup_app_l.
          { done. }
          { word. }
        }
        rewrite H1.
        apply list_prefix_forall.
        { done. }
        { done. }
      }
    }
    {
      iMod ("Hvalid" $! σ' Hprefix_old with "Hσ'") as "Hσ".
      iInv "Hinv" as "Hi" "Hclose".
      iDestruct "Hi" as "[Hupd|#>Hlb]"; last first.
      {
        iDestruct (own_valid_2 with "Hσ Hlb") as "%Hvalid".
        exfalso.
        rewrite mono_list_both_dfrac_valid_L in Hvalid.
        destruct Hvalid as [_ Hvalid].
        apply prefix_length in Hvalid.
        rewrite app_length in Hvalid.
        simpl in Hvalid.
        word.
      }
      iDestruct "Hupd" as "[>Hlc Hupd]".
      iMod (lc_fupd_elim_later with "Hlc Hupd" ) as "Hupd".
      iMod (fupd_mask_subseteq (⊤∖↑ghostN)) as "Hmask".
      {
        assert ((↑sysN:coPset) ⊆ (↑ghostN:coPset)).
        { apply nclose_subseteq. }
        assert ((↑opN:coPset) ⊆ (↑ghostN:coPset)).
        { apply nclose_subseteq. }
        set_solver.
      }
      iMod "Hupd".
      iDestruct "Hupd" as (?) "[Hghost Hupd]".
      iDestruct (own_valid_2 with "Hghost Hσ") as %Hvalid.
      rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
      destruct Hvalid as [_ ->].
      iCombine "Hghost Hσ" as "Hσ".
      iMod (own_update with "Hσ") as "Hσ".
      {
        apply (mono_list_update (st.(mp_log) ++ [entry] : list (leibnizO EntryType))).
        by apply prefix_app_r.
      }
      iEval (rewrite -Qp.half_half) in "Hσ".
      rewrite -dfrac_op_own.
      rewrite mono_list_auth_dfrac_op.
      iDestruct "Hσ" as "[Hσ Hcommit]".
      iSpecialize ("Hupd" with "[] Hσ").
      { done. }
      iMod "Hupd".

      rewrite mono_list_auth_lb_op.
      iDestruct "Hcommit" as "[Hcommit #Hlb]".
      iMod "Hmask".
      iMod ("Hclose" with "[]").
      {
        iNext.
        iRight.
        iFrame "Hlb".
      }
      iModIntro.
      iFrame.
    }
    {
      rewrite Hlatest.
      by iFrame.
    }
  }
  iModIntro.
  iFrame "#".
Qed.

Lemma ghost_replica_get_lb γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  is_accepted_lb γsrv st.(mp_acceptedEpoch) st.(mp_log).
Proof.
  by iNamed 1.
Qed.

(* Similar to ghost_accept in pb_ghost.v *)
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
  intros Hineq1 Hineq2 Hlen.
  iNamed 1.
  iIntros "#Hprop_lb2 #Hprop_facts2".
  iAssert (⌜st.(mp_epoch) = epoch'⌝)%I as "%HepochEq".
  { iPureIntro. word. }
  iFrame "%".
  destruct (decide _); last first.
  {
    exfalso. naive_solver.
  }

  iDestruct (own_valid_2 with "Hprop_lb Hprop_lb2") as %Hcomp.
  rewrite -HepochEq in Hcomp.
  replace (st.(mp_acceptedEpoch)) with (st.(mp_epoch)) in Hcomp by word.

  rewrite singleton_op singleton_valid in Hcomp.
  rewrite -Cinr_op Cinr_valid in Hcomp.
  rewrite mono_list_lb_op_valid_L in Hcomp.

  assert (st.(mp_log)⪯log').
  {
    destruct Hcomp as [Hbad|Hcomp]; first done.
    enough (log'=st.(mp_log)) by naive_solver.
    by apply list_prefix_eq.
  }
  rewrite -e.

  iMod (own_update with "Hacc") as "Hacc".
  {
    apply singleton_update.
    apply mono_list_update.
    instantiate (1:=log').
    done.
  }
  iClear "Hacc_lb".
  iDestruct (own_mono _ _
               {[ st.(mp_epoch) := (◯ML _) ]}
              with "Hacc") as "#Hacc_lb".
  {
    apply singleton_mono.
    apply mono_list_included.
  }

  iModIntro.
  replace st.(mp_epoch) with epoch' by word.
  replace st.(mp_acceptedEpoch) with epoch' by word.
  unfold own_replica_ghost.
  simpl.
  rewrite decide_True; last done.
  iFrame "∗#".
  iSplitL; first done.
  iIntros (?).
  exfalso.
  lia.
Qed.

Lemma ghost_replica_accept_same_epoch_old γsys γsrv st epoch' log' :
  int.nat st.(mp_epoch) ≤ int.nat epoch' →
  int.nat st.(mp_acceptedEpoch) = int.nat epoch' →
  length log' ≤ length st.(mp_log) →
  own_replica_ghost γsys γsrv st -∗
  is_proposal_lb γsys epoch' log' -∗
  is_accepted_lb γsrv epoch' log'.
Proof.
  intros Hineq1 Heq2 Hlen.
  iNamed 1.
  iIntros "#Hprop_lb2".
  iAssert (⌜st.(mp_epoch) = epoch'⌝)%I as "%HepochEq".
  { iPureIntro. word. }
  iFrame "%".
  destruct (decide _); last first.
  {
    exfalso. naive_solver.
  }

  iDestruct (own_valid_2 with "Hprop_lb Hprop_lb2") as %Hcomp.
  rewrite -HepochEq in Hcomp.
  replace (st.(mp_acceptedEpoch)) with (st.(mp_epoch)) in Hcomp by word.

  rewrite singleton_op singleton_valid in Hcomp.
  rewrite -Cinr_op Cinr_valid in Hcomp.
  rewrite mono_list_lb_op_valid_L in Hcomp.

  assert (log'⪯st.(mp_log)).
  {
    destruct Hcomp as [Hbad|Hcomp]; last done.
    enough (log'=st.(mp_log)) by naive_solver.
    symmetry.
    by apply list_prefix_eq.
  }
  replace (st.(mp_acceptedEpoch)) with epoch' by word.

  iDestruct (own_mono _ _
               {[ epoch' := (◯ML _) ]}
              with "Hacc_lb") as "$".
  {
    apply singleton_mono.
    apply mono_list_lb_mono.
    done.
  }
Qed.

Lemma ghost_replica_accept_new_epoch γsys γsrv st epoch' log' :
  int.nat st.(mp_epoch) ≤ int.nat epoch' →
  int.nat st.(mp_acceptedEpoch) ≠ int.nat epoch' →
  own_replica_ghost γsys γsrv st -∗
  is_proposal_lb γsys epoch' log' -∗
  is_proposal_facts γsys epoch' log'
  ==∗
  own_replica_ghost γsys γsrv (mkMPaxosState epoch' epoch' log').
Proof.
  intros Hineq1 Hneq2.
  iNamed 1.
  iIntros "#Hprop_lb2 #Hprop_facts2".
  assert (int.nat st.(mp_epoch) < int.nat epoch' ∨ int.nat st.(mp_epoch) = int.nat epoch') as Hcases.
  { word. }
  destruct Hcases as [HnewEpoch|HcurrentEpoch].
  { (* case: mp_acceptedEpoch < mp_epoch == epoch'; get stuff out of Hunused *)
    iClear "Hacc".
    iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hacc Hunused]".
    { set_solver. }
    iSpecialize ("Hacc" with "[%//]").
    iMod (own_update with "Hacc") as "Hacc".
    {
      apply singleton_update.
      apply mono_list_update.
      instantiate (1:=log').
      apply prefix_nil.
    }
    iModIntro.
    iDestruct (own_mono _ _ {[ epoch' := (◯ML _) ]}
                with "Hacc") as "#Hacc_lb2".
    { apply singleton_mono. apply mono_list_included. }
    unfold own_replica_ghost.
    simpl.
    destruct (decide _); last first.
    { exfalso. done. }
    iFrame "Hacc #".
    iSplitR; first done.
    iSplitR.
    { iIntros (?). exfalso. lia. }
    iSplitL "Hunused".
    {
      iApply "Hunused".
      {
        iModIntro.
        iIntros (???) "Hwand".
        iIntros (Hy).
        iApply "Hwand".
        iPureIntro. word.
      }
      {
        iIntros.
        exfalso. lia.
      }
    }
    iApply (big_sepS_impl with "Hvotes").
    iModIntro.
    iIntros (??) "[%|$]".
    iLeft.
    iPureIntro. word.
  }
  { (* case: mp_acceptedEpoch < mp_epoch == epoch'; use existing acc *)
    destruct (decide _).
    { exfalso. word. }

    iMod (own_update with "Hacc") as "Hacc".
    {
      apply singleton_update.
      apply mono_list_update.
      instantiate (1:=log').
      apply prefix_nil.
    }
    iModIntro.
    replace st.(mp_epoch) with (epoch') by word.
    iDestruct (own_mono _ _ {[ epoch' := (◯ML _) ]}
                with "Hacc") as "#Hacc_lb2".
    { apply singleton_mono. apply mono_list_included. }

    unfold own_replica_ghost.
    simpl.
    destruct (decide _); last first.
    { exfalso. done. }
    iFrame "Hacc #".
    iSplitR; first done.
    iSplitR.
    { iIntros (?). exfalso. lia. }
    iSplitL "Hunused".
    {
      iApply (big_sepS_impl with "Hunused").
      iModIntro.
      iIntros (??) "Hwand".
      iIntros (?).
      iApply "Hwand".
      iPureIntro. word.
    }
    {
      iApply (big_sepS_impl with "Hvotes").
      iModIntro.
      iIntros (??) "[%|$]".
      iLeft.
      iPureIntro. word.
    }
  }
Qed.

(* TODO: this is just the definition *)
Lemma establish_committed_by epoch σ (W:gset nat) :
  (∀ s, s ∈ W → s < length config) →
  2 * (size W) > length config →
  ([∗ list] s0↦γsrv' ∈ config, ⌜s0 ∈ W⌝ → is_accepted_lb γsrv' epoch σ) -∗
  committed_by epoch σ.
Proof.
  iIntros.
  iExists _; iFrame "∗#%".
Qed.

Definition sys_inv γsys := inv sysN
(
  ∃ σ epoch,
  own_commit γsys σ ∗
  committed_by epoch σ ∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ
).

(* copy/pasted almost verbatin from ghost_commit in pb_ghost.v! *)
Lemma ghost_commit γsys epoch σ :
  sys_inv γsys -∗
  committed_by epoch σ -∗
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ
  ={⊤}=∗ (* XXX: this is ⊤ because the user-provided fupd is fired, and it is allowed to know about ⊤ *)
  is_ghost_lb γsys σ.
Proof.
  iIntros "#Hinv #Hcom #Hprop_lb #Hprop_facts".
  iInv "Hinv" as "Hown" "Hclose".
  iDestruct "Hown" as (σcommit epoch_commit) "(>Hghost & >#Hcom_com & >#Hprop_lb_com & #Hprop_facts_com)".
  iDestruct "Hprop_facts_com" as "(>Hmax_com & Hvalid_com)".
  iDestruct "Hprop_facts" as "(Hmax & Hvalid)".
  iAssert (⌜σcommit ⪯ σ⌝ ∨ ⌜σ ⪯ σcommit⌝)%I as "%Hlog".
  {
    assert (int.nat epoch < int.nat epoch_commit ∨ int.nat epoch = int.nat epoch_commit ∨ int.nat epoch > int.nat epoch_commit) as [Hepoch|[Hepoch|Hepoch]]by word.
    { (* case epoch < epoch_commit: use old_proposal_max of epoch_commit. *)
      iRight.
      by iApply "Hmax_com".
    }
    { (* case epoch = epoch_commit: proposal is comparable *)
      replace (epoch) with (epoch_commit) by word.
      iDestruct (own_valid_2 with "Hprop_lb Hprop_lb_com") as %Hvalid.
      rewrite singleton_op in Hvalid.
      rewrite singleton_valid in Hvalid.
      apply mono_list_lb_op_valid_1_L in Hvalid.
      iPureIntro.
      naive_solver.
    }
    { (* case epoch_commit < epoch: use old_proposal_max of epoch *)
      iLeft.
      by iApply "Hmax".
    }
  }

  destruct Hlog as [Hcan_update|Halready_updated].
  {
    iEval (unfold is_proposal_valid) in "Hvalid".
    iDestruct ("Hvalid" $! σcommit with "[] Hghost") as "Hghost".
    { done. }
    iMod "Hghost".
    unfold own_commit.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost $]".
    iMod ("Hclose" with "[-]").
    {
      iNext.
      iExists _, _. iFrame "∗".
      iFrame "Hcom".
      iFrame "#".
    }
    done.
  }
  {
    unfold own_commit.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost #Hlb]".
    iDestruct (own_mono with "Hlb") as "$".
    {
      by apply mono_list_lb_mono.
    }
    iMod ("Hclose" with "[-]").
    {
      iNext.
      iExists _, _. iFrame "∗#".
    }
    done.
  }
Qed.

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
  intros Hle.
  iIntros "Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hro & #Hskip)".
  iExists _; iFrame "Hro".
  iSplitR.
  {
    iPureIntro.
    by transitivity log.
  }
  iModIntro.
  iIntros.
  iApply "Hskip".
  { iPureIntro. word. }
  { iPureIntro. word. }
Qed.

Lemma is_proposal_lb_compare γsys log log' epoch :
  length log' ≤ length log →
  is_proposal_lb γsys epoch log -∗
  is_proposal_lb γsys epoch log' -∗
  ⌜prefix log' log⌝
.
Proof.
  intros Hlen.
  iIntros "Hprop1 Hprop2".
  iDestruct (own_valid_2 with "Hprop1 Hprop2") as %Hcomp.
  rewrite singleton_op singleton_valid in Hcomp.
  rewrite -Cinr_op Cinr_valid in Hcomp.
  rewrite mono_list_lb_op_valid_L in Hcomp.
  destruct Hcomp as [Hbad|Hcomp]; last done.
  enough (log'=log) by naive_solver.
  symmetry.
  by apply list_prefix_eq.
Qed.

Definition validSet (W:gset nat) :=
  ∀ s, s ∈ W → s < length config.

Lemma validSet_union (W1 W2:gset nat) :
  validSet W1 →
  validSet W2 →
  validSet (W1 ∪ W2).
Proof.
  intros.
  intros ??.
  apply elem_of_union in H1 as [|].
  { naive_solver. }
  { naive_solver. }
Qed.

Lemma validSet_size (W:gset nat) :
  validSet W →
  size W ≤ length config.
Proof.
  rewrite /validSet.
  revert W.
  induction (length config) as [| n IHn] => W Hvalid.
  - destruct W as [| x W] using set_ind_L; auto.
    exfalso. feed pose proof (Hvalid x); first by set_solver. lia.
  - transitivity (size ({[n]} ∪ (W ∖ {[n]}))).
    { apply subseteq_size. set_unfold. intros x. destruct (decide (x = n)); auto. }
    rewrite size_union ?size_singleton; last by set_solver.
    feed pose proof (IHn (W ∖ {[n]})).
    { set_unfold. intros x (Hin&?). feed pose proof (Hvalid x); auto. lia. }
    lia.
Qed.

Definition vote_inv γsys := inv sysN
(
  [∗ set] e ∈ (fin_to_set u64),
  (∃ (W:gset nat), ⌜validSet W⌝ ∗ ⌜2 * (size W) > length config⌝ ∗
  [∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv e) ∨
  own_proposal γsys e []
).

Lemma quorum_overlap W1 W2 :
  validSet W1 →
  2 * (size W1) > length config →
  validSet W2 →
  2 * (size W2) > length config →
  ∃ x γsrv, x ∈ W1 ∧ x ∈ W2 ∧
            config !! x = Some γsrv
.
Proof.
  intros HW Hquorum  HW2 Hquorum2.
  destruct (decide ((W1 ∩ W2) = ∅)).
  { (* case: the proposal has already been claimed; this should be impossible *)
    exfalso.
    pose proof (size_union W1 W2) as H.
    assert (W1 ## W2).
    { set_solver. }
    apply H in H0.
    pose proof (validSet_union _ _ HW HW2) as HuValid.
    apply validSet_size in HuValid.
    word.
  }
  {
    apply set_choose_L in n.
    destruct n as [s Hs].
    apply elem_of_intersection in Hs as [HsW HsW2].
    (* get a vote out of Hvotes1 and Hvotes2, then contradiction *)
    assert (s < length config).
    { apply HW. done. }
    pose proof (list_lookup_lt _ _ _ H) as [γsrv' Hlookup].
    exists s, γsrv'.
    done.
  }
Qed.

Lemma get_proposal_from_votes γsys (W:gset nat) newEpoch :
  2 * (size W) > length config →
  validSet W →
  vote_inv γsys -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv newEpoch) ={↑sysN}=∗
  own_proposal γsys newEpoch [].
Proof.
  intros Hquorum HW.
  iIntros "#Hinv Hvotes".
  iInv "Hinv" as ">Hi" "Hclose".
  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "Hi") as "[Hprop Hi]".
  { set_solver. }
  iDestruct "Hprop" as "[Hbad|Hprop]".
  {
    iDestruct "Hbad" as (W2) "(%HW2 & %Hquorum2 & Hvotes2)".
    pose proof (quorum_overlap _ _ HW Hquorum HW2 Hquorum2) as [? [? [? []]]].

    iDestruct (big_sepL_lookup_acc with "Hvotes") as "[Hvote1 _]".
    { done. }
    iSpecialize ("Hvote1" with "[%//]").
    iDestruct (big_sepL_lookup_acc with "Hvotes2") as "[Hvote2 _]".
    { done. }
    iSpecialize ("Hvote2" with "[%//]").
    iDestruct (own_valid_2 with "Hvote1 Hvote2") as %Hbad.
    exfalso.
    rewrite singleton_op in Hbad.
    rewrite singleton_valid in Hbad.
    apply dfrac_agree_op_valid_L in Hbad as [Hbad _].
    done.
  }
  iFrame "Hprop".
  iMod ("Hclose" with "[Hi Hvotes]").
  {
    iApply ("Hi" with "[] [Hvotes]").
    {
      iModIntro.
      iIntros.
      iFrame.
    }
    {
      iLeft.
      iExists _; iFrame.
      done.
    }
  }
  done.
Qed.

Lemma accepted_upper_bound_lb γsrv acceptedEpoch newEpoch log log':
  is_accepted_lb γsrv acceptedEpoch log -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch -∗
  ⌜log ⪯ log'⌝
.
Proof.
  iIntros "#Hacc_lb #Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro & Hacc_ub)".
  iDestruct (own_valid_2 with "Hacc_ro Hacc_lb") as %Hvalid.
  rewrite singleton_op singleton_valid in Hvalid.
  rewrite mono_list_both_dfrac_valid_L in Hvalid.
  destruct Hvalid as [_ [ Hvalid]].
  iPureIntro.
  assert (log ⪯ logPrefix).
  {
    rewrite H.
    by apply prefix_app_r.
  }
  eapply transitivity.
  { done. }
  { done. }
Qed.

Lemma accepted_upper_bound_lb2 γsrv acceptedEpoch epoch newEpoch log log':
  int.nat acceptedEpoch < int.nat epoch →
  int.nat epoch < int.nat newEpoch →
  is_accepted_lb γsrv epoch log -∗
  is_accepted_upper_bound γsrv log' acceptedEpoch newEpoch -∗
  ⌜log ⪯ log'⌝
.
Proof.
  intros Hineq Hineq2.
  iIntros "#Hacc_lb #Hacc_ub".
  iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro & #Hacc_ub)".
  iSpecialize ("Hacc_ub" $! epoch with "[%//] [%//]").

  iDestruct (own_valid_2 with "Hacc_ub Hacc_lb") as %Hvalid.
  rewrite singleton_op singleton_valid in Hvalid.
  rewrite mono_list_both_dfrac_valid_L in Hvalid.
  destruct Hvalid as [_ [ Hvalid]].
  iPureIntro.
  symmetry in H.
  apply app_eq_nil in H as [-> ].
  apply prefix_nil.
Qed.

(* This is where the magic happens *)
Lemma become_leader γsys (W:gset nat) latestLog acceptedEpoch newEpoch:
  validSet W →
  2 * (size W) > length config →
  vote_inv γsys -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → is_accepted_upper_bound γsrv latestLog acceptedEpoch newEpoch) -∗
  is_proposal_lb γsys acceptedEpoch latestLog -∗
  is_proposal_facts γsys acceptedEpoch latestLog -∗
  ([∗ list] s↦γsrv ∈ config, ⌜s ∈ W⌝ → own_vote_tok γsrv newEpoch) ={↑sysN}=∗
  own_leader_ghost γsys (mkMPaxosState newEpoch newEpoch latestLog)
.
Proof.
  intros HW Hquorum.
  iIntros "#Hinv #Hacc #Hprop_lb #Hprop_facts Hvotes".

  iMod (get_proposal_from_votes with "Hinv Hvotes") as "Hprop".
  { done. }
  { done. }

  iMod (own_update with "Hprop") as "Hprop".
  {
    apply singleton_update.
    apply csum_update_r.
    apply mono_list_update.
    instantiate (1:=latestLog).
    apply prefix_nil.
  }

  iFrame "Hprop".
  iDestruct "Hprop_facts" as "[Hmax Hvalid]".
  iFrame "Hvalid".

  (* establish old_proposal_max *)
  iModIntro.
  iIntros (?).
  iModIntro.
  simpl.
  iIntros (? HepochIneq) "#Hcom_old".

  destruct (decide (int.nat epoch_old < int.nat acceptedEpoch)).
  { (* case: epoch_old < acceptedEpoch, just use prev old_prop_max *)
    iApply "Hmax".
    { done. }
    iFrame "Hcom_old".
  }

  iDestruct "Hcom_old" as (W2) "(%HW2 & %Hquorum2 & Hcom_old)".
  (* note that W and W2 overlap *)
  pose proof (quorum_overlap _ _ HW Hquorum HW2 Hquorum2) as [? [? [? []]]].
  iDestruct (big_sepL_lookup_acc with "Hacc") as "[Hacc_ub _ ]".
  { done. }
  iSpecialize ("Hacc_ub" with "[%//]").
  iDestruct (big_sepL_lookup_acc with "Hcom_old") as "[Hacc_lb _]".
  { done. }
  iSpecialize ("Hacc_lb" with "[%//]").

  destruct (decide (int.nat acceptedEpoch = int.nat epoch_old)).
  { (* case: epoch_old = acceptedEpoch *)
    replace (acceptedEpoch) with (epoch_old); last first.
    {
      assert (int.Z acceptedEpoch = int.Z epoch_old) by word.
      naive_solver. (* XXX: why do I have to assert this Z inequalit? *)
    } (* we have int.nat a = int.nat b, and need to show a = b *)
    iDestruct (accepted_upper_bound_lb with "Hacc_lb Hacc_ub") as %Hineq.
    done.
  }
  { (* case: acceptedEpoch < epoch_old < newEpoch *)
    assert (int.nat acceptedEpoch < int.nat epoch_old) as Hineq by word.
    iDestruct (accepted_upper_bound_lb2 with "Hacc_lb Hacc_ub") as %Hineq2.
    { done. }
    { done. }
    done.
  }
Qed.

Lemma ghost_leader_get_proposal γsys st :
  own_leader_ghost γsys st -∗
  is_proposal_lb γsys st.(mp_epoch) st.(mp_log) ∗
  is_proposal_facts γsys st.(mp_epoch) st.(mp_log)
.
Proof.
  iNamed 1.
  iFrame "#".
  iDestruct (own_mono with "Hprop") as "$".
  {
    apply singleton_included.
    right.
    apply Cinr_included.
    apply mono_list_included.
  }
Qed.

Lemma ghost_replica_helper1 γsys γsrv st :
  own_replica_ghost γsys γsrv st -∗
  ⌜int.nat st.(mp_acceptedEpoch) ≤ int.nat st.(mp_epoch)⌝.
Proof.
  iNamed 1.
  iPureIntro.
  done.
Qed.

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
  intros Hineq.
  iNamed 1.

  (* FIXME: take points-tos out of Hunused, with e < newEpoch *)
  set (F1:=(λ e, (⌜int.nat e > int.nat st.(mp_epoch)⌝ → ⌜int.nat e < int.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  set (F2:=(λ e, (⌜int.nat e > int.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  set (F3:=(λ e, (⌜int.nat e = int.nat newEpoch⌝ → own_accepted γsrv e []))%I).
  iDestruct (big_sepS_impl with "Hunused []") as "Hunused".
  {
    instantiate (1:=(λ e, (F1 e ∗ F3 e) ∗ F2 e)%I).
    iModIntro.
    iIntros (??) "Hwand".
    unfold F1. unfold F2. unfold F3.
    destruct (decide (int.nat x < int.nat newEpoch)).
    {
      iSplitL "Hwand".
      {
        iSplitL "Hwand".
        { iIntros. iApply "Hwand". iPureIntro. word. }
        { iIntros. exfalso. word. }
      }
      { iIntros. exfalso. word. }
    }
    {
      destruct (decide (int.nat x = int.nat newEpoch)).
      {
        iSplitL "Hwand".
        {
          iSplitR "Hwand".
          { iIntros. exfalso. word. }
          { iIntros. iApply "Hwand". iPureIntro. word. }
        }
        { iIntros. exfalso. word. }
    }
    {
      assert (int.nat x > int.nat newEpoch) by word.
      iSplitR "Hwand".
      {
        iSplitL.
        { iIntros. exfalso. word. }
        { iIntros. exfalso. word. }
      }
      { iIntros. iApply "Hwand". iPureIntro. word. }
    }
    }
  }
  simpl.
  iDestruct (big_sepS_sep with "Hunused") as "[Hunused HunusedNew]".
  unfold F2.
  iDestruct (big_sepS_sep with "Hunused") as "[Hunused HunusedSingle]".
  (* Now, we can do whatever we want with Hunused (F1); let's freeze it all! *)

  set (G1:=(λ (e:u64),
        |==> (⌜int.nat e > int.nat st.(mp_epoch)⌝
          → ⌜int.nat e < int.nat newEpoch⌝ -∗
          is_accepted_ro γsrv e [])%I
                  )%I).
  iDestruct (big_sepS_impl with "Hunused []") as "Hunused".
  {
    iModIntro.
    instantiate (1:=G1).
    iIntros (??) "Hwand".
    unfold F1.
    unfold G1.

    destruct (decide (int.nat st.(mp_epoch) < int.nat x)); last first.
    {
      iModIntro.
      iIntros. exfalso; word.
    }
    destruct (decide (int.nat x < int.nat newEpoch)); last first.
    {
      iModIntro.
      iIntros. exfalso; word.
    }
    iSpecialize ("Hwand" with "[%//] [%//]").

    iMod (own_update with "Hwand") as "$"; last done.
    apply singleton_update.
    apply mono_list_auth_persist.
  }
  unfold G1.
  iMod (big_sepS_bupd with "Hunused") as "#Hunused".

  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "HunusedSingle") as "[Hacc2 _]".
  { set_solver. }
  iSpecialize ("Hacc2" with "[%//]").
  iDestruct (big_sepS_elem_of_acc_impl newEpoch with "Hvotes") as "[Hvote Hvotes]".
  { set_solver. }
  iDestruct "Hvote" as "[%Hbad|Hvote]".
  { exfalso. word. }

  iAssert (|==> is_accepted_upper_bound γsrv st.(mp_log) st.(mp_acceptedEpoch) newEpoch)%I with "[Hacc Hunused]" as ">#Hacc_ub2".
  {
    destruct (decide _).
    { (* case: need to freeze *)
      iMod (own_update with "Hacc") as "Hacc".
      {
        apply singleton_update.
        apply mono_list_auth_persist.
      }
      iDestruct "Hacc" as "#Hacc_ro".

      iModIntro.
      iExists st.(mp_log).
      iSplit; first done.
      replace st.(mp_epoch) with st.(mp_acceptedEpoch) by word.
      iFrame "#".
      iModIntro.
      iIntros.
      iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hunused2 _]".
      { set_solver. }
      iApply "Hunused2".
      { iPureIntro. word. }
      { iPureIntro. word. }
    }
    {
      iMod (own_update with "Hacc") as "Hacc".
      {
        apply singleton_update.
        apply mono_list_auth_persist.
      }
      iDestruct "Hacc" as "#Hacc_ro".
      iSpecialize ("Hacc_ub" with "[%]").
      { word. }
      iDestruct "Hacc_ub" as (?) "(%Hpre & #Hacc_ro2 & #Hacc_ub)".
      iExists _.
      iModIntro.
      iSplit; first iPureIntro.
      { done. }
      iFrame "Hacc_ro2".
      iModIntro.
      iIntros.
      destruct (decide (int.nat epoch' < int.nat st.(mp_epoch))).
      { iApply "Hacc_ub"; done. }
      assert (int.nat st.(mp_epoch) ≤ int.nat epoch') by word.

      iDestruct (big_sepS_elem_of_acc_impl epoch' with "Hunused") as "[Hunused2 _]".
      { set_solver. }
      destruct (decide (int.nat epoch' = int.nat st.(mp_epoch))).
      {
        replace (epoch') with (st.(mp_epoch)) by word.
        iFrame "#".
      }
      iApply "Hunused2".
      { iPureIntro. word. }
      { iPureIntro. word. }
    }
  }

  iModIntro.
  iFrame "Hvote".
  iFrame "Hprop_lb Hprop_facts Hacc_lb".
  simpl.
  destruct (decide _).
  { exfalso. word. }
  iFrame "Hacc2".
  iFrame "#".
  iSplitR; first iPureIntro.
  { word. }
  iSplitR; first done.
  iFrame "HunusedNew".
  iApply "Hvotes".
  {
    iModIntro.
    iIntros (???) "[%|$]".
    iLeft.
    iPureIntro. word.
  }
  {
    iLeft.
    iPureIntro. word.
  }
Qed.

End mpaxos_protocol.
