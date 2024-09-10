From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.Helpers Require Import ListSolver.
From Perennial.algebra Require Export fmlist_map.

Section pb_protocol.

Record pb_system_names :=
{
  pb_proposal_gn : gname ;
  pb_config_gn : gname;
  pb_config_prop_gn : gname;
  pb_state_gn : gname ;
}.

Record pb_server_names :=
{
  pb_epoch_gn: gname ;
  pb_accepted_gn : gname ;
}.

Context `{EntryType:Type}.
Local Canonical Structure EntryTypeO := leibnizO EntryType.
Local Definition logR := mono_listR EntryType.

Class pb_ghostG Σ := {
    #[global] pb_ghost_epochG :: mono_natG Σ ;
    #[global] pb_ghost_map_logG :: fmlist_mapG Σ u64 EntryType;
    #[global] pb_ghost_commitG :: inG Σ logR ;
    #[global] pb_ghost_configG :: inG Σ (gmapR u64 (dfrac_agreeR (leibnizO (option (list pb_server_names))))) ;
}.

Definition pb_ghostΣ :=
  #[mono_natΣ ; fmlist_mapΣ u64 EntryType ;
    GFunctor (gmapR (u64) logR) ;
    GFunctor logR ;
    GFunctor (gmapR u64 (dfrac_agreeR (leibnizO (option (list pb_server_names)))))
    ].
Global Instance subG_pb_ghostΣ {Σ} : subG (pb_ghostΣ) Σ → (pb_ghostG Σ).
Proof. solve_inG. Qed.

Context `{!gooseGlobalGS Σ}.
Context `{!pb_ghostG Σ}.

Implicit Type γsrv : pb_server_names.
Implicit Type γsys : pb_system_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(pb_epoch_gn) 1 (uint.nat epoch).
Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(pb_epoch_gn) (uint.nat epoch).

Definition own_proposal_unused γsys epoch : iProp Σ :=
  epoch ⤳l[γsys.(pb_proposal_gn)] [].
Definition own_proposal γsys epoch σ : iProp Σ :=
  epoch ⤳l[γsys.(pb_proposal_gn)] σ.
Definition is_proposal_lb γsys epoch σ : iProp Σ :=
  epoch ⤳l[γsys.(pb_proposal_gn)]⪰ σ.

Notation "lhs ⪯ rhs" := (prefix lhs rhs)
(at level 20, format "lhs  ⪯  rhs") : stdpp_scope.

Definition own_accepted γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(pb_accepted_gn)] σ.
Definition is_accepted_lb γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(pb_accepted_gn)]⪰ σ.
Definition is_accepted_ro γ epoch σ : iProp Σ :=
  epoch ⤳l[γ.(pb_accepted_gn)]□ σ.

(* NOTE: if desired, can make these exclusive by adding an exclusive token to each *)
Definition own_pb_log γ σ : iProp Σ :=
  own γ.(pb_state_gn) (●ML{#1/2} σ).
Definition is_pb_log_lb γ σ : iProp Σ :=
  own γ.(pb_state_gn) (◯ML σ).

Definition config_proposal_unset γ (epoch:u64) : iProp Σ :=
  own γ.(pb_config_prop_gn) {[epoch := (to_dfrac_agree (DfracOwn 1) (None : (leibnizO _)))]}.
Definition is_epoch_config_proposal γ epoch (conf:list pb_server_names): iProp Σ :=
  own γ.(pb_config_prop_gn) {[ epoch := (to_dfrac_agree DfracDiscarded (Some conf : (leibnizO _)))]} ∗
  ⌜length conf > 0⌝.

Definition is_epoch_config γ epoch (conf:list pb_server_names): iProp Σ :=
  own γ.(pb_config_gn) {[ epoch := (to_dfrac_agree DfracDiscarded (Some conf : (leibnizO _)))]} ∗
  is_epoch_config_proposal γ epoch conf.
Definition is_epoch_skipped γ epoch : iProp Σ :=
  own γ.(pb_config_gn) {[ epoch := (to_dfrac_agree DfracDiscarded (None : (leibnizO _)))]}.
Definition config_unset γ (epoch:u64) : iProp Σ :=
  own γ.(pb_config_gn) {[epoch := (to_dfrac_agree (DfracOwn 1) (None : (leibnizO _)))]}.


Definition committed_by γsys epoch σ : iProp Σ :=
  ∃ conf, is_epoch_config γsys epoch conf ∗
      ∀ γsrv, ⌜γsrv ∈ conf⌝ → is_accepted_lb γsrv epoch σ.

Definition old_proposal_max γsys epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜uint.nat epoch_old < uint.nat epoch⌝ →
   committed_by γsys epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition pbN := nroot .@ "pb".
Definition pb_protocolN := pbN .@ "protocol".
Definition ghostN := pb_protocolN .@ "ghost".

Definition sysN := ghostN .@ "sys".
Definition opN := ghostN .@ "op".

(* XXX(namespaces):
   The update for the ghost state is fired while the is_repl_inv is open.
   Additionally, the update is fired while the is_valid_inv is open, so we need
   the initial mask to exclude those invariants.
*)
Definition is_valid_inv γsys σ op : iProp Σ :=
  inv opN (
    £ 1 ∗
    (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_pb_log γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_pb_log γsys (someσ ++ [op]) ={∅,⊤∖↑ghostN}=∗ True)) ∨
    is_pb_log_lb γsys (σ ++ [op])
  )
.

(* XXX: this definition of is_proposal_valid allows for the committed state to
   be partially updated to any intermediate op. So, we have to be able to fire
   one update at a time with is_valid_inv and ghost_propose has to append one
   operation at a time.
 *)
Definition is_proposal_valid γ σ : iProp Σ :=
  □(∀ σ', ⌜σ' ⪯ σ⌝ → own_pb_log γ σ' ={⊤∖↑sysN}=∗ own_pb_log γ σ).

Definition is_proposal_facts γ epoch σ: iProp Σ :=
  old_proposal_max γ epoch σ ∗
  is_proposal_valid γ σ.

Definition own_replica_ghost γsys γsrv epoch σ (sealed:bool) : iProp Σ :=
  "Hepoch_ghost" ∷ own_epoch γsrv epoch ∗
  "Haccepted" ∷ (if sealed then True else own_accepted γsrv epoch σ) ∗
  "#Haccepted_ro" ∷ □(if sealed then is_accepted_ro γsrv epoch σ else True) ∗
  "Haccepted_rest" ∷ ([∗ set] e' ∈ (fin_to_set u64), ⌜uint.nat e' ≤ uint.nat epoch⌝ ∨
                                                      own_accepted γsrv e' []) ∗
  "#Hproposal_lb" ∷ is_proposal_lb γsys epoch σ ∗
  "#Hvalid" ∷ is_proposal_facts γsys epoch σ
.

Definition own_primary_ghost γsys epoch σ : iProp Σ :=
  "Hprop" ∷ own_proposal γsys epoch σ ∗
  "#Hvalid" ∷ is_proposal_facts γsys epoch σ
.

Lemma ghost_accept_and_unseal γsys γsrv sealed epoch epoch' σ' σ :
  uint.nat epoch < uint.nat epoch' →
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  is_proposal_lb γsys epoch' σ' -∗
  is_proposal_facts γsys epoch' σ'
  ==∗
  own_replica_ghost γsys γsrv epoch' σ' false.
Proof.
  intros Hineq.
  iIntros "Hown #Hprop_lb #Hprop_facts".
  iNamed "Hown".
  iSplitL "Hepoch_ghost".
  {
    iDestruct (mono_nat_own_update with "Hepoch_ghost") as "[$ _]".
    word.
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
    iApply (fmlist_ptsto_update with "Haccepted").
    apply prefix_nil.
  }
  iSplitR; first done.
  iApply "Haccepted_rest".
  {
    iModIntro.
    iIntros (???) "[%Hineq2|$]".
    iLeft.
    iPureIntro.
    word.
  }
  iLeft.
  done.
Qed.

Lemma ghost_get_proposal_facts γsys γsrv epoch σ sealed :
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ.
Proof. iNamed 1. iFrame "#". Qed.

Lemma ghost_accept_lb_ineq γsys γsrv epoch sealed σ σ' :
  is_accepted_lb γsrv epoch σ' -∗
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  ⌜σ' ⪯ σ⌝.
Proof.
  iIntros "#?". iNamed 1.
  destruct sealed.
  { by iApply (fmlist_ptsto_lb_agree with "Haccepted_ro"). }
  { by iApply (fmlist_ptsto_lb_agree with "Haccepted"). }
Qed.

Lemma ghost_accept γsys γsrv epoch epoch' σ σ' :
  uint.nat epoch ≤ uint.nat epoch' →
  length σ ≤ length σ' →
  own_replica_ghost γsys γsrv epoch σ false -∗
  is_proposal_lb γsys epoch' σ' -∗
  is_proposal_facts γsys epoch' σ'
  ==∗
  own_replica_ghost γsys γsrv epoch' σ' false.
Proof.
  intros Hepoch_ineq Hσlen_ineq.
  iIntros "Hown #Hprop_lb #Hprop_facts".

  destruct (decide (epoch = epoch')).
  {
    subst.
    iNamed "Hown".
    iDestruct (fmlist_ptsto_lb_longer with "Hproposal_lb Hprop_lb") as %Hσ_ineq.
    { done. }
    iFrame "Hepoch_ghost".
    iFrame "Haccepted_rest".
    iFrame "Hprop_lb".
    iFrame "Hprop_facts".
    by iMod (fmlist_ptsto_update with "Haccepted") as "$".
  }
  {
    iApply (ghost_accept_and_unseal with "Hown Hprop_lb Hprop_facts").
    assert (uint.nat epoch < uint.nat epoch' ∨ uint.nat epoch = uint.nat epoch') as [|] by word.
    { done. }
    { exfalso. assert (epoch = epoch') by word. done. }
  }
Qed.

Lemma ghost_seal γsys γsrv sealed epoch σ :
  own_replica_ghost γsys γsrv epoch σ sealed ==∗
  own_replica_ghost γsys γsrv epoch σ true.
Proof.
  iNamed 1.
  iFrame "∗#".
  destruct sealed.
  { by iFrame "#". }
  {
    iMod (fmlist_ptsto_persist with "Haccepted") as "#$".
    done.
  }
Qed.

Lemma ghost_get_accepted_ro γsys γsrv epoch σ :
  own_replica_ghost γsys γsrv epoch σ true -∗
  is_accepted_ro γsrv epoch σ.
Proof.
  by iNamed 1.
Qed.

Lemma ghost_helper1 γsys γsrv epoch σ1 σ2 sealed:
  length σ1 = length σ2 →
  is_proposal_lb γsys epoch σ1 -∗
  own_replica_ghost γsys γsrv epoch σ2 sealed -∗
  ⌜σ1 = σ2⌝.
Proof.
  intros Hlen.
  iIntros "#Hprop_lb".
  iNamed 1.
  by iDestruct (fmlist_ptsto_lb_len_eq with "Hprop_lb Hproposal_lb") as %Hcomp.
Qed.

Lemma ghost_epoch_lb_ineq γsys γsrv epoch epoch_lb σ sealed:
  is_epoch_lb γsrv epoch_lb -∗
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  ⌜uint.nat epoch_lb ≤ uint.nat epoch⌝.
Proof.
  iIntros "#Hlb".
  iNamed 1.
  by iDestruct (mono_nat_lb_own_valid with "Hepoch_ghost Hlb") as %[_ Hineq].
Qed.

(* Used by ApplyAsBackup *)
Lemma ghost_accept_helper2 γsys γsrv epoch σ σ_old sealed:
  is_proposal_lb γsys epoch σ -∗
  own_replica_ghost γsys γsrv epoch σ_old sealed -∗
  own_replica_ghost γsys γsrv epoch σ_old sealed ∗
  ⌜σ ⪯ σ_old ∨ σ_old ⪯ σ⌝
.
Proof.
  iIntros "#Hprop Hghost".
  iNamed "Hghost".
  iDestruct (fmlist_ptsto_lb_comparable with "Hprop Hproposal_lb") as %Hσ_ineq.
  iFrame "∗#%".
Qed.

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
  subst.
  rewrite length_app /= in Hlen.
  assert (length σ' = length σ_old) by lia.
  iDestruct (fmlist_ptsto_lb_mono with "Hprop_lb") as "#Hprop'_lb".
  { by exists [newOp]. }
  iDestruct (fmlist_ptsto_lb_len_eq with "Hprop'_lb Hproposal_lb") as %Hσ_ineq.
  { done. }
  subst.
  iFrame "∗#".
  done.
Qed.

Lemma ghost_get_accepted_lb γsys γsrv epoch σ sealed :
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  is_accepted_lb γsrv epoch σ.
Proof.
  iNamed 1.
  iAssert (∃ dq, epoch ⤳l[γsrv.(pb_accepted_gn)]{dq} σ)%I with "[Haccepted]" as (?) "HH".
  {
    destruct sealed.
    { iExists _; iFrame "∗#". }
    { iExists _; iFrame "∗#". }
  }
  iDestruct (fmlist_ptsto_get_lb with "HH") as "$".
Qed.

Lemma ghost_get_epoch_lb γsys γsrv epoch σ sealed :
  own_replica_ghost γsys γsrv epoch σ sealed -∗
  is_epoch_lb γsrv epoch.
Proof. iNamed 1. by iApply mono_nat_lb_own_get. Qed.

(* FIXME: this should be in some general file *)
Lemma prefix_app_cases {A} (σ σ':list A) e:
  σ' `prefix_of` σ ++ [e] →
  σ' `prefix_of` σ ∨ σ' = (σ++[e]).
Proof.
  intros [σ0 Heq].
  induction σ0 using rev_ind.
  { rewrite app_nil_r in Heq. right; congruence. }
  { rewrite app_assoc in Heq.
    apply app_inj_2 in Heq as [-> ?]; last auto.
    left. eexists; eauto.
  }
Qed.

Lemma valid_add γsys σ op :
  £ 1 -∗
  is_proposal_valid γsys σ -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_pb_log γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_pb_log γsys (someσ++[op]) ={∅,⊤∖↑ghostN}=∗ True))
  ={↑pb_protocolN}=∗
  is_proposal_valid γsys (σ++[op]).
Proof.
  iIntros "Hlc #Hvalid Hupd".
  unfold is_proposal_valid.
  iAssert (|={↑pb_protocolN}=> is_valid_inv γsys σ op)%I with "[Hupd Hlc]" as ">#Hinv".
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
  apply prefix_app_cases in Hσ' as [Hprefix_old|Hlatest].
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
      rewrite length_app in Hvalid.
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
      apply (mono_list_update (σ ++ [op])).
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

Lemma ghost_propose γsys epoch σ op :
  £ 1 -∗
  own_primary_ghost γsys epoch σ -∗
  (|={⊤∖↑ghostN,∅}=> ∃ someσ, own_pb_log γsys someσ ∗ (⌜someσ = σ⌝ -∗ own_pb_log γsys (someσ++[op]) ={∅,⊤∖↑ghostN}=∗ True))
  ={↑pb_protocolN}=∗
  own_primary_ghost γsys epoch (σ++[op]) ∗
  is_proposal_lb γsys epoch (σ++[op]) ∗
  is_proposal_facts γsys epoch (σ++[op])
.
Proof.
  iIntros "Hlc Hown Hupd".
  iNamed "Hown".

  iMod (fmlist_ptsto_update (σ++[op]) with "Hprop") as "Hprop".
  { by apply prefix_app_r. }

  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "#Hprop_lb".
  iFrame "Hprop".
  iAssert (|={↑pb_protocolN}=> is_proposal_facts γsys epoch (σ++[op]))%I with "[Hupd Hlc]" as ">#Hvalid2".
  {
    iDestruct "Hvalid" as "[#Hmax #Hvalid]".
    iSplitR.
    {
      iModIntro.
      unfold old_proposal_max.
      iModIntro.
      iIntros.
      iAssert (⌜σ_old ⪯ σ⌝)%I as "%Hprefix2".
      {
        iApply "Hmax".
        {
          done.
        }
        { iFrame "#". }
      }
      iPureIntro.
      transitivity σ.
      { done. }
      by apply prefix_app_r.
    }
    {
      by iMod (valid_add with "Hlc Hvalid Hupd") as "#$".
    }
  }
  iModIntro.
  iFrame "#".
Qed.

Lemma ghost_propose_lb_valid γsys epoch σ σ' :
  own_primary_ghost γsys epoch σ -∗
  is_proposal_lb γsys epoch σ' -∗
  ⌜σ' ⪯ σ⌝
.
Proof.
  iIntros "Hprim Hprop_lb".
  iNamed "Hprim".
  iApply (fmlist_ptsto_lb_agree with "Hprop Hprop_lb").
Qed.

Definition is_repl_inv γsys := inv sysN
(
  ∃ σ epoch,
  own_pb_log γsys σ ∗
  committed_by γsys epoch σ ∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ
).

(*
  User will get their (Q) by knowing (is_ghost_lb γ σ) where (op, Q) ∈ σ.
 *)
Lemma ghost_commit γsys epoch σ :
  is_repl_inv γsys -∗
  committed_by γsys epoch σ -∗
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ
  ={⊤}=∗ (* XXX: this is ⊤ because the user-provided fupd is fired, and it is allowed to know about ⊤ *)
  is_pb_log_lb γsys σ.
Proof.
  iIntros "#Hinv #Hcom #Hprop_lb #Hprop_facts".
  iInv "Hinv" as "Hown" "Hclose".
  iDestruct "Hown" as (σcommit epoch_commit) "(>Hghost & >#Hcom_com & >#Hprop_lb_com & #Hprop_facts_com)".
  iDestruct "Hprop_facts_com" as "(>Hmax_com & Hvalid_com)".
  iDestruct "Hprop_facts" as "(Hmax & Hvalid)".
  iAssert (⌜σcommit ⪯ σ⌝ ∨ ⌜σ ⪯ σcommit⌝)%I as "%Hlog".
  {
    assert (uint.nat epoch < uint.nat epoch_commit ∨ uint.nat epoch = uint.nat epoch_commit ∨ uint.nat epoch > uint.nat epoch_commit) as [Hepoch|[Hepoch|Hepoch]]by word.
    { (* case epoch < epoch_commit: use old_proposal_max of epoch_commit. *)
      iRight.
      by iApply "Hmax_com".
    }
    { (* case epoch = epoch_commit: proposal is comparable *)
      replace (epoch) with (epoch_commit) by word.
      iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hprop_lb_com") as %Hvalid.
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
    unfold own_pb_log.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost $]".
    iMod ("Hclose" with "[-]").
    {
      iNext. iExists _, _. iFrame "∗ Hcom #".
    }
    done.
  }
  {
    unfold own_pb_log.
    iEval (rewrite mono_list_auth_lb_op) in "Hghost".
    iDestruct "Hghost" as "[Hghost #Hlb]".
    iDestruct (own_mono with "Hlb") as "$".
    { by apply mono_list_lb_mono. }
    iMod ("Hclose" with "[-]").
    {
      iNext. iExists _, _. iFrame "∗#".
    }
    done.
  }
Qed.

Lemma ghost_get_propose_lb_facts γsys epoch σ :
  own_primary_ghost γsys epoch σ -∗
  is_proposal_lb γsys epoch σ ∗
  is_proposal_facts γsys epoch σ.
Proof.
  iNamed 1. iFrame "#".
  by iApply fmlist_ptsto_get_lb.
Qed.

Lemma ghost_init_primary γsys γsrv σ epochconf epoch conf epoch_new :
  γsrv ∈ conf →
  uint.nat epoch < uint.nat epoch_new →
  uint.nat epochconf ≤ uint.nat epoch →
  is_proposal_lb γsys epoch σ -∗
  is_proposal_facts γsys epoch σ -∗
  is_epoch_config γsys epochconf conf -∗
  is_accepted_ro γsrv epoch σ -∗
  (∀ epoch_skip, ⌜uint.nat epochconf < uint.nat epoch_skip⌝ → ⌜uint.nat epoch_skip < uint.nat epoch_new⌝ → is_epoch_skipped γsys epoch_skip) -∗
  own_proposal_unused γsys epoch_new
  ==∗
  own_primary_ghost γsys epoch_new σ
.
Proof.
  intros Hmember Hepoch_new Hepoch_recent.
  iIntros "#Hprop_lb #Hprop_facts #His_conf #Hacc_ro #Hskip Hprop".
  iMod (fmlist_ptsto_update σ with "Hprop") as "Hprop".
  { apply prefix_nil. }
  iFrame "Hprop".
  iDestruct "Hprop_facts" as "[Hmax $]".

  iModIntro.
  iIntros (epoch_old σ_old).
  iModIntro.
  iIntros (Hepoch).
  iIntros "#Hcom_old".
  assert (uint.nat epoch_old < uint.nat epoch ∨ uint.nat epoch_old = uint.nat epoch ∨ uint.nat epoch < uint.nat epoch_old ) as Hcases.
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
    assert (uint.nat epochconf = uint.nat epoch ∨ uint.nat epochconf < uint.nat epoch) as [Heq|Hineq] by word.
    {
      replace (epochconf) with (epoch) by word.
      iDestruct (own_valid_2 with "Hconf_old His_conf") as %Hvalid.
      rewrite singleton_op singleton_valid dfrac_agree_op_valid in Hvalid.
      destruct Hvalid as [_ Hvalid].
      replace (conf_old) with (conf) by naive_solver.
      iSpecialize ("Hcom_old" $! γsrv with "[//]").
      clear Hvalid.
      iApply (fmlist_ptsto_lb_agree with "Hacc_ro Hcom_old").
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

Lemma is_epoch_conf_agree γsys epoch conf1 conf2 :
  is_epoch_config γsys epoch conf1 -∗
  is_epoch_config_proposal γsys epoch conf2 -∗
  ⌜conf1 = conf2⌝
.
Proof.
  iIntros "(_ & H & _) (? & _)".
  iDestruct (own_valid_2 with "[$] [$]") as %?.
  iPureIntro.
  rewrite singleton_op singleton_valid dfrac_agree_op_valid_L in H.
  destruct H as [_ H]; naive_solver.
Qed.

Lemma alloc_const_gmap {A:cmra} (a:A) `{H:inG Σ (gmapR u64 A)} :
  (✓a) →
    ⊢ |==> ∃ γ, [∗ set] epoch ∈ (fin_to_set u64), own γ {[ epoch := a ]}
.
Proof.
  intros Havalid.
  set (m:=(gset_to_gmap a (fin_to_set u64))).
  iMod (own_alloc m) as (γ) "H".
  { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
    rewrite Some_valid. done. }

  iAssert ([∗ set] epoch ∈ fin_to_set u64,
            own γ {[ epoch := a ]}
          )%I with "[H]" as "H".
  {
    rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace (fin_to_set u64) with (dom m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "H").
    iIntros "!#" (k x). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ [= <-]]).
    iIntros "$".
  }
  iModIntro.
  iExists _; iFrame.
Qed.

Definition pb_init_for_config γsys confγs : iProp Σ :=
  "#His_conf" ∷ is_epoch_config γsys 0 confγs ∗
  "#His_conf_prop" ∷ is_epoch_config_proposal γsys 0 confγs ∗
  (* "#His_hosts" ∷ ([∗ list] γsrv ; host ∈ confγs ; conf, is_pb_host host γpb γsrv) ∗ *)
  "#His_lbs" ∷ (∀ γsrv, ⌜γsrv ∈ confγs⌝ → is_epoch_lb γsrv 0) ∗
  "Hunused" ∷ ([∗ set] epoch' ∈ (fin_to_set u64), ⌜uint.nat 0 < uint.nat epoch'⌝ →
              config_proposal_unset γsys epoch' ∗ config_unset γsys epoch' ∗
              own_proposal_unused γsys epoch'
              ).

Definition is_sys_init_witness γsys : iProp Σ :=
  is_proposal_lb γsys (W64 0) [] ∗ is_proposal_facts γsys (W64 0) [].

Lemma pb_system_init (confγs:list pb_server_names) :
length confγs > 0 →
(∀ γsrv, ⌜γsrv ∈ confγs⌝ → is_accepted_lb γsrv (W64 0) [] ∗ is_epoch_lb γsrv 0) ={⊤}=∗
    ∃ γsys,
    is_repl_inv γsys ∗
    own_pb_log γsys [] ∗
    pb_init_for_config γsys confγs ∗
    is_sys_init_witness γsys
.
Proof.
  intros Hlen.
  iIntros "#Hacc".
  (* allocate ghost state, and establish is_repl_inv *)
  iMod (own_alloc (●ML [])) as "Hghost".
  { apply mono_list_auth_valid. }
  iDestruct "Hghost" as (γstate) "[Hghost Hghost2]".
  unfold pb_init_for_config.
  iMod (fmlist_map_alloc_fin []) as (γproposal) "Hproposal".
  iMod (alloc_const_gmap (to_dfrac_agree (DfracOwn 1)
                                         (None : leibnizO (option (list pb_server_names)))
       )) as (γconfig) "Hconfig".
  { done. }
  iMod (alloc_const_gmap (to_dfrac_agree (DfracOwn 1)
                                         (None : leibnizO (option (list pb_server_names)))
       )) as (γconfig_proposal) "Hconfig_prop".
  { done. }

  (* set up proposal for epoch 0 *)
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hproposal") as "[Hprop Hprop_rest]".
  { set_solver. }
  iDestruct (fmlist_ptsto_get_lb with "Hprop") as "#Hprop_lb".

  (* set up initial config proposal *)
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hconfig_prop") as "[Hconfig_prop Hconfig_prop_rest]".
  { set_solver. }
  iMod (own_update with "Hconfig_prop") as "Hconf_prop".
  {
    apply singleton_update.
    instantiate (1:=(to_dfrac_agree (DfracDiscarded) (Some confγs : leibnizO _))).
    apply cmra_update_exclusive.
    done.
  }
  iDestruct "Hconf_prop" as "#Hconf_prop".

  (* set up initial config *)
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hconfig") as "[Hconfig Hconfig_rest]".
  { set_solver. }
  iMod (own_update with "Hconfig") as "Hconf".
  {
    apply singleton_update.
    instantiate (1:=(to_dfrac_agree (DfracDiscarded) (Some confγs : leibnizO _))).
    apply cmra_update_exclusive.
    done.
  }
  iDestruct "Hconf" as "#Hconf".

  set  (γsys:= {|
      pb_proposal_gn := γproposal ;
      pb_config_gn := γconfig ;
      pb_config_prop_gn := γconfig_proposal ;
      pb_state_gn := γstate ;
    |}).
  iExists γsys.
  simpl.

  iAssert (is_proposal_facts
    {|
      pb_proposal_gn := γproposal;
      pb_config_gn := γconfig;
      pb_config_prop_gn := γconfig_proposal;
      pb_state_gn := γstate
    |} 0%Z []) with "[]" as "#Hprop_facts".
  {
    iSplit.
    {
      iIntros (???).
      exfalso.
      replace (uint.nat (W64 0)) with (0) in H by word.
      lia.
    }
    iModIntro.
    iIntros (??).
    iIntros "Hcom".
    apply prefix_nil_inv in H.
    rewrite H.
    iFrame.
    done.
  }

  iMod (inv_alloc with "[Hghost2]") as "$".
  { (* establish is_repl_inv *)
    iNext.
    iExists [], (W64 0).
    simpl.
    iFrame "∗#".
    iSplitL; first done.
    iIntros (??).
    iDestruct ("Hacc" $! _ H) as "[$ _]".
  }
  iModIntro.
  iFrame "∗#".
  iSplitR; first done.
  iSplitR; first done.
  iSplitR.
  {
    iIntros (??).
    iDestruct ("Hacc" $! γsrv H) as "[_ $]".
  }

  rewrite /own_proposal_unused /config_unset /config_proposal_unset /=.
  iSpecialize ("Hprop_rest" $! (λ epoch, ⌜uint.nat 0 < uint.nat epoch⌝ → own_proposal_unused γsys epoch)%I with "[] []").
  {
    iModIntro.
    iIntros.
    iFrame.
  }
  { iIntros. exfalso. replace (uint.nat (W64 0)) with (0) in H by word. lia. }

  iSpecialize ("Hconfig_prop_rest" $! (λ epoch, ⌜uint.nat 0 < uint.nat epoch⌝ → config_proposal_unset γsys epoch)%I with "[] []").
  {
    iModIntro.
    iIntros.
    iFrame.
  }
  { iIntros. exfalso. replace (uint.nat (W64 0)) with (0) in H by word. lia. }

  iSpecialize ("Hconfig_rest" $! (λ epoch, ⌜uint.nat 0 < uint.nat epoch⌝ → config_unset γsys epoch)%I with "[] []").
  {
    iModIntro.
    iIntros.
    iFrame.
  }
  { iIntros. exfalso. replace (uint.nat (W64 0)) with (0) in H by word. lia. }

  iDestruct (big_sepS_sep_2 with "Hprop_rest Hconfig_prop_rest") as "HH".
  iDestruct (big_sepS_sep_2 with "HH Hconfig_rest") as "HH".
  iApply (big_sepS_impl with "HH").
  iModIntro.
  iIntros (??) "[[H1 H2] H3]".
  iIntros (Hineq).
  iDestruct ("H1" $! Hineq) as "$".
  iDestruct ("H2" $! Hineq) as "$".
  iDestruct ("H3" $! Hineq) as "$".
Qed.

Definition own_server_pre γsrv : iProp Σ :=
  "Hepoch" ∷ own_epoch γsrv 0 ∗
  "Haccepted" ∷ own_accepted γsrv 0 [] ∗
  "Haccepted_rest" ∷ ([∗ set] e' ∈ (fin_to_set u64), ⌜uint.nat e' ≤ uint.nat 0⌝ ∨
                                                      own_accepted γsrv e' [])
.

Lemma pb_ghost_server_pre_init :
  ⊢ |==> ∃ γsrv, own_server_pre γsrv ∗ is_accepted_lb γsrv (W64 0) [] ∗ is_epoch_lb γsrv (W64 0)
.
Proof.
  iMod (fmlist_map_alloc_fin []) as (γacc) "Hacc".
  iMod (mono_nat_own_alloc 0) as (γepoch) "[Hepoch Hepoch_lb]".
  iDestruct (big_sepS_elem_of_acc_impl (W64 0) with "Hacc") as "[Hacc Haccrest]".
  { set_solver. }
  iDestruct (fmlist_ptsto_get_lb with "Hacc") as "#Hacc_lb".

  iExists {| pb_epoch_gn := _ ; pb_accepted_gn := _ ; |}.
  iModIntro.
  iFrame "∗#".
  iApply "Haccrest".
  {
    iModIntro.
    iIntros.
    iFrame.
  }
  {
    iLeft. done.
  }
Qed.

(* Right order of allocation:
  Allocate the purely local state of each server.
  Use that to pick the config for epoch 0.
  Set up system state and is_repl_inv.
  Finish setting up local state, how that is_repl_inv is available.
*)

Lemma pb_ghost_server_init γsys γsrv :
  is_sys_init_witness γsys -∗
  own_server_pre γsrv
  -∗
  own_replica_ghost γsys γsrv (W64 0) [] false
.
Proof.
  iIntros "[#Hprop_lb #Hfacts] Hown".
  iNamed "Hown".
  by iFrame "∗#%".
Qed.

Lemma pb_log_get_nil_lb γsys :
  is_repl_inv γsys ={↑pb_protocolN}=∗
  is_pb_log_lb γsys [].
Proof.
  iIntros "#Hinv".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as (??) "[>Hlog ?]".
  unfold own_pb_log.
  iEval (rewrite mono_list_auth_lb_op) in "Hlog".
  iDestruct "Hlog" as "[Hlog #Hlb]".
  iDestruct (own_mono with "Hlb") as "$".
  { apply mono_list_lb_mono. apply prefix_nil. }
  iMod ("Hclose" with "[-]"); last done.
  { eauto with iFrame. }
Qed.

End pb_protocol.
