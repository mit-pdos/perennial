From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.Helpers Require Import ListSolver.

Section pb_protocol.

Context `{!heapGS Σ}.

Record pb_system_names :=
{
  pb_proposal_gn : gname ; (* system-wide *)
  pb_config_gn : gname; (* system-wide *)
  pb_state_gn : gname ; (* system-wide *)
}.

Record pb_server_names :=
{
  urpc_gn: server_chan_gnames ;
  pb_epoch_gn: gname ;
  pb_accepted_gn : gname ;
}.

Context `{EntryType:Type}.

Local Definition logR := mono_listR (leibnizO EntryType).

Class pb_ghostG Σ := {
    pb_ghost_epochG :> mono_natG Σ ;
    pb_ghost_proposalG :> inG Σ (gmapR (u64) logR) ;
    pb_ghost_commitG :> inG Σ logR ;
    pb_ghost_configG :> inG Σ (gmapR u64 (dfrac_agreeR (leibnizO (option (list pb_server_names))))) ;
}.

Context `{!pb_ghostG Σ}.

Implicit Type γsrv : pb_server_names.
Implicit Type γsys : pb_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(pb_epoch_gn) 1 (int.nat epoch).
Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(pb_epoch_gn) (int.nat epoch).

Definition own_proposal γsys epoch σ : iProp Σ :=
  own γsys.(pb_proposal_gn) {[ epoch := ●ML (σ : list (leibnizO (EntryType)))]}.
Definition is_proposal_lb γsys epoch σ : iProp Σ :=
  own γsys.(pb_proposal_gn) {[ epoch := ◯ML (σ : list (leibnizO (EntryType)))]}.

Definition own_accepted γ epoch σ : iProp Σ :=
  own γ.(pb_accepted_gn) {[ epoch := ●ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_lb γ epoch σ : iProp Σ :=
  own γ.(pb_accepted_gn) {[ epoch := ◯ML (σ : list (leibnizO (EntryType)))]}.
Definition is_accepted_ro γ epoch σ : iProp Σ :=
  own γ.(pb_accepted_gn) {[ epoch := ●ML□ (σ : list (leibnizO (EntryType)))]}.

(* TODO: if desired, can make these exclusive by adding an exclusive token to each *)
Definition own_ghost γ σ : iProp Σ :=
  own γ.(pb_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition own_commit γ σ : iProp Σ :=
  own γ.(pb_state_gn) (●ML{#1/2} (σ : list (leibnizO (EntryType)))).
Definition is_ghost_lb γ σ : iProp Σ :=
  own γ.(pb_state_gn) (◯ML (σ : list (leibnizO (EntryType)))).

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

Definition is_epoch_config γ epoch (conf:list pb_server_names): iProp Σ :=
  own γ.(pb_config_gn) {[ epoch := (to_dfrac_agree DfracDiscarded (Some conf : (leibnizO _)))]} ∗
  ⌜length conf > 0⌝.
Definition is_epoch_skipped γ epoch : iProp Σ :=
  own γ.(pb_config_gn) {[ epoch := (to_dfrac_agree DfracDiscarded (None : (leibnizO _)))]}.
Definition config_unset γ (epoch:u64) : iProp Σ :=
  own γ.(pb_config_gn) {[epoch := (to_dfrac_agree (DfracOwn (1/2)) (None : (leibnizO _)))]}.

Definition committed_by γsys epoch σ : iProp Σ :=
  ∃ conf, is_epoch_config γsys epoch conf ∗
      ∀ γsrv, ⌜γsrv ∈ conf⌝ → is_accepted_lb γsrv epoch σ.

Definition old_proposal_max γsys epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜int.nat epoch_old < int.nat epoch⌝ →
   committed_by γsys epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition pbN := nroot .@ "pb".
Definition ghostN := pbN .@ "ghost".

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

Definition own_replica_ghost γsys γsrv epoch σ (sealed:bool) : iProp Σ :=
  "Hepoch_ghost" ∷ own_epoch γsrv epoch ∗
  "Haccepted" ∷ own_accepted γsrv epoch σ ∗
  "Haccepted_rest" ∷ ([∗ set] e' ∈ (fin_to_set u64), ⌜int.nat e' ≤ int.nat epoch⌝ ∨
                                                      own_accepted γsrv e' []) ∗
  "#Hproposal_lb" ∷ is_proposal_lb γsys epoch σ ∗
  "#Hvalid" ∷ is_proposal_facts γsys epoch σ
.

Lemma ghost_accept γsys γsrv epoch epoch' σ σ' :
  int.nat epoch ≤ int.nat epoch' →
  length σ ≤ length σ' →
  own_replica_ghost γsys γsrv epoch σ false -∗
  is_proposal_lb γsys epoch' σ' -∗
  is_proposal_facts γsys epoch' σ'
  ==∗
  own_replica_ghost γsys γsrv epoch' σ' false.
Proof.
  intros Hepoch_ineq Hσlen_ineq.
  iIntros "Hown #Hprop_lb #Hprop_facts".
  iNamed "Hown".

  destruct (decide (epoch = epoch')).
  {
    iDestruct (own_valid_2 with "Hprop_lb Hproposal_lb") as %Hσ_ineq.
    rewrite e in Hσ_ineq.
    rewrite singleton_op singleton_valid in Hσ_ineq.
    rewrite mono_list_lb_op_valid_L in Hσ_ineq.
    assert (σ⪯σ').
    {
      destruct Hσ_ineq as [Hbad|Hσ_ineq]; last done.
      enough (σ'=σ) by naive_solver.
      by apply list_prefix_eq.
    }
    rewrite -e.
    iFrame "Hepoch_ghost".
    iFrame "Haccepted_rest".
    iFrame "Hprop_lb".
    iFrame "Hprop_facts".
    iApply (own_update with "Haccepted").
    apply singleton_update.
    apply mono_list_update.
    done.
  }
  {
    assert (int.nat epoch < int.nat epoch') as Hepoch_new.
    {
      assert (int.nat epoch < int.nat epoch' ∨ int.nat epoch = int.nat epoch') as [|] by word.
      { done. }
      { exfalso. assert (epoch = epoch') by word. done. }
    }
    iSplitL "Hepoch_ghost".
    {
      iDestruct (mono_nat_own_update with "Hepoch_ghost") as "[$ _]".
      done.
    }
    iFrame "Hprop_lb Hprop_facts".
    iDestruct (big_sepS_elem_of_acc_impl epoch' with "Haccepted_rest") as "[HH Haccepted_rest]".
    { set_solver. }
    iClear "Haccepted".
    iDestruct "HH" as "[%Hbad|Haccepted]".
    {
      exfalso.
      word.
    }
    iSplitL "Haccepted".
    {
      iApply (own_update with "Haccepted").
      apply singleton_update.
      apply mono_list_update.
      apply prefix_nil.
    }
    iApply "Haccepted_rest".
    {
      iModIntro.
      iIntros (???) "[%Hineq|$]".
      iLeft.
      iPureIntro.
      word.
    }
    iLeft.
    done.
  }
Qed.

(* Used by ApplyAsBackup *)
Lemma ghost_accept_helper newOp γsys γsrv epoch σ σ_old sealed:
  length σ = length σ_old + 1 →
  last σ = Some newOp →
  is_proposal_lb γsys epoch σ -∗
  own_replica_ghost γsys γsrv epoch σ_old sealed -∗
  own_replica_ghost γsys γsrv epoch σ_old sealed ∗
  ⌜σ = σ_old ++ [newOp]⌝
.
Proof.
  intros Hlen Hlast.
  iIntros "#Hprop_lb Hghost".
  iNamed "Hghost".
  rewrite last_Some in Hlast.
  destruct Hlast as [σ' Hlast].
  assert (length σ' + 1 = length σ).
  {
    rewrite Hlast.
    rewrite app_length.
    done.
  }
  assert (length σ' = length σ_old) by lia.
  iDestruct (own_mono with "Hprop_lb") as "#Hprop'_lb".
  {
    instantiate (1:={[epoch := ◯ML (σ' : list (leibnizO EntryType))]}).
    rewrite singleton_included.
    right.
    apply mono_list_lb_mono.
    by exists [newOp].
  }
  iDestruct (own_valid_2 with "Hprop'_lb Hproposal_lb") as %Hσ_ineq.
  rewrite singleton_op singleton_valid in Hσ_ineq.
  rewrite mono_list_lb_op_valid_L in Hσ_ineq.
  assert (σ' = σ_old).
  {
    destruct Hσ_ineq as [|].
    {
      apply list_prefix_eq.
      { done. }
      word.
    }
    {
      symmetry.
      apply list_prefix_eq.
      { done. }
      word.
    }
  }
  iFrame "∗#".
  rewrite -H1.
  iPureIntro.
  done.
Qed.

Lemma ghost_get_accepted_lb γsys γsrv epoch σ sealed :
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  is_accepted_lb γsrv epoch σ.
Proof.
  iNamed 1.
  unfold own_accepted.
  (* FIXME: how to get lower bound? *)
  (* rewrite mono_list_auth_lb_op. *)
  admit.
Admitted.

Lemma ghost_get_propose_lb γsys epoch σ :
  own_proposal γsys epoch σ -∗
  is_proposal_lb γsys epoch σ.
Proof.
Admitted.

Lemma ghost_propose γsys epoch σ op :
  own_proposal γsys epoch σ -∗
  is_proposal_facts γsys epoch σ -∗
  £ 1 -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_ghost γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γsys (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True))
  ={⊤}=∗
  own_proposal γsys epoch (σ ++ [op]) ∗
  (is_proposal_facts γsys epoch (σ ++ [op])).
Proof.
  iIntros "Hprop #Hprop_facts Hlc Hupd".
  iSplitL "Hprop".
  {
    iApply (own_update with "Hprop").
    apply singleton_update.
    apply mono_list_update.
    apply prefix_app_r.
    done.
  }
  unfold is_proposal_facts.
  iSplitL "".
  {
    iDestruct "Hprop_facts" as "[#Hmax _]".
    iModIntro.
    unfold old_proposal_max.
    iModIntro.
    iIntros.
    iAssert (⌜σ_old ⪯ σ⌝)%I as "%Hprefix".
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
  iDestruct "Hprop_facts" as "[_ #Hvalid]".
  unfold is_proposal_valid.

  iAssert (|={⊤}=> is_valid_inv γsys σ op)%I with "[Hupd Hlc]" as ">#Hinv".
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
  assert (σ' ⪯ σ ∨ σ' = (σ ++ [op])) as [Hprefix_old|Hlatest].
  { (* TODO: list_solver. *)
    assert (Hlen := Hσ').
    apply prefix_length in Hlen.
    assert (length σ' = length (σ ++ [op]) ∨ length σ' < length (σ ++ [op])) as [|] by word.
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
      assert (σ !! i = (σ ++ [op]) !! i).
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
      apply (mono_list_update (σ ++ [op] : list (leibnizO EntryType))).
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
Qed.

Definition sys_inv γsys := inv sysN
(
  ∃ σ epoch,
  own_commit γsys σ ∗
  committed_by γsys epoch σ ∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ
).

(*
  User will get their (Q) by knowing (is_ghost_lb γ σ) where (op, Q) ∈ σ.
 *)
Lemma ghost_commit γsys epoch σ :
  sys_inv γsys -∗
  committed_by γsys epoch σ -∗
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ
  ={⊤}=∗ (* XXX: this is ⊤ because the user-provided fupd is fired, and it is allowed to know about ⊤ *)
  is_ghost_lb γsys σ.
Proof.
  iIntros "#Hinv #Hcom #Hprop_lb #Hprop_facts".
  iInv "Hinv" as "Hown" "Hclose".
  iDestruct "Hown" as (σcommit epoch_commit) "(>Hghost & >#Hcom_com & >#Hprop_lb_com & #Hprop_facts_com)".
  iDestruct "Hprop_facts_com" as "[>Hmax_com Hvalid_com]".
  iDestruct "Hprop_facts" as "[Hmax Hvalid]".
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

Lemma ghost_become_leader γsys γsrv σ epochconf epoch conf epoch_new :
  γsrv ∈ conf →
  int.nat epoch < int.nat epoch_new →
  int.nat epochconf ≤ int.nat epoch →
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ -∗
  is_epoch_config γsys epochconf conf -∗
  is_accepted_ro γsrv epoch σ -∗
  (∀ epoch_skip, ⌜int.nat epochconf < int.nat epoch_skip⌝ → ⌜int.nat epoch_skip < int.nat epoch_new⌝ → is_epoch_skipped γsys epoch_skip) -∗
  own_proposal γsys epoch_new []
  ==∗
  own_proposal γsys epoch_new σ ∗
  is_proposal_facts γsys epoch_new σ
.
Proof.
  intros Hmember Hepoch_new Hepoch_recent.
  iIntros "#Hprop_lb #Hprop_facts #His_conf #Hacc_ro #Hskip Hprop".
  iMod (own_update with "Hprop") as "Hprop".
  {
    apply singleton_update.
    apply mono_list_update.
    instantiate (1:=σ : list (leibnizO _)).
    apply prefix_nil.
  }
  iFrame "Hprop".
  iDestruct "Hprop_facts" as "[Hmax $]".

  iModIntro.
  iIntros (epoch_old σ_old).
  iModIntro.
  iIntros (Hepoch).
  iIntros "#Hcom_old".
  assert (int.nat epoch_old < int.nat epoch ∨ int.nat epoch_old = int.nat epoch ∨ int.nat epoch < int.nat epoch_old ) as Hcases.
  { word. }
  destruct Hcases as [Hineq|[HepochEq|Hineq]].
  { (* for old enough epochs, use existing old_prop_max *)
    iApply "Hmax".
    { done. }
    { iFrame "#". }
  }
  {
    replace (epoch_old) with (epoch) by word.
    iDestruct "Hcom_old" as (conf_old) "[Hconf_old Hcom_old]".
    iDestruct "Hconf_old" as "[Hconf_old _]".
    iDestruct "His_conf" as "[His_conf _]".
    assert (int.nat epochconf = int.nat epoch ∨ int.nat epochconf < int.nat epoch) as [Heq|Hineq] by word.
    {
      replace (epochconf) with (epoch) by word.

      iDestruct (own_valid_2 with "Hconf_old His_conf") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid in Hvalid.
      destruct Hvalid as [_ Hvalid].
      replace (conf_old) with (conf) by naive_solver.
      iSpecialize ("Hcom_old" $! γsrv with "[//]").
      clear Hvalid.
      iDestruct (own_valid_2 with "Hacc_ro Hcom_old") as %Hvalid.
      iPureIntro.
      rewrite singleton_op singleton_valid in Hvalid.
      rewrite mono_list_both_dfrac_valid_L in Hvalid.
      naive_solver.
    }
    {
      iSpecialize ("Hskip" $! epoch with "[% //] [% //]").
      iDestruct (own_valid_2 with "Hskip Hconf_old") as %Hbad.
      exfalso.
      rewrite singleton_op in Hbad.
      rewrite singleton_valid in Hbad.
      rewrite dfrac_agree_op_valid in Hbad.
      destruct Hbad as [_ Hbad].
      done.
    }
  }
  { (* skipped epochs; prove False *)
    unfold committed_by.
    iDestruct "Hcom_old" as (conf_old) "[#Hconf_old _]".
    iSpecialize ("Hskip" $! epoch_old with "[%] [//]").
    { word. }
    iExFalso.
    (* Hconf_old and Hskip are contradictory *)
    iDestruct "Hconf_old" as "[Hconf_old _]".
    iDestruct (own_valid_2 with "Hconf_old Hskip") as %Hbad.
    exfalso.
    rewrite singleton_op in Hbad.
    rewrite singleton_valid in Hbad.
    rewrite dfrac_agree_op_valid in Hbad.
    naive_solver.
  }
Qed.

End pb_protocol.
