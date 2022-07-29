From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.goose_lang Require Import crash_borrow.
From Perennial.Helpers Require Import ListSolver.

Section pb_protocol.

Context `{!heapGS Σ}.

Record pb_server_names :=
{
  urpc_gn: server_chan_gnames ;
  pb_epoch_gn: gname ;
  pb_accepted_gn : gname ;
  pb_proposal_gn : gname ; (* system-wide *)
  pb_config_gn : gname; (* system-wide *)
  pb_state_gn : gname ; (* system-wide *)
}.

Context `{EntryType:Type}.

Local Definition logR := mono_listR (leibnizO EntryType).

Class pbG Σ := {
    pb_epochG :> mono_natG Σ ;
    pb_proposalG :> inG Σ (gmapR (u64) logR) ;
    pb_commitG :> inG Σ logR ;
    pb_configG :> inG Σ (gmapR u64 (dfrac_agreeR (leibnizO (list pb_server_names)))) ;
}.

Context `{!pbG Σ}.

Implicit Type γ : pb_server_names.
Implicit Type σ : list EntryType.
Implicit Type epoch : u64.

Definition own_epoch γ (epoch:u64) : iProp Σ :=
  mono_nat_auth_own γ.(pb_epoch_gn) 1 (int.nat epoch).
Definition is_epoch_lb γ (epoch:u64) : iProp Σ :=
  mono_nat_lb_own γ.(pb_epoch_gn) (int.nat epoch).

Definition own_proposal γ epoch σ : iProp Σ :=
  own γ.(pb_proposal_gn) {[ epoch := ●ML (σ : list (leibnizO (EntryType)))]}.
Definition is_proposal_lb γ epoch σ : iProp Σ :=
  own γ.(pb_proposal_gn) {[ epoch := ◯ML (σ : list (leibnizO (EntryType)))]}.

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
(at level 20, format "lhs ⪯ rhs") : stdpp_scope.

Definition is_epoch_config γ epoch (conf:list pb_server_names): iProp Σ :=
  own γ.(pb_config_gn) {[ epoch := to_dfrac_agree DfracDiscarded (conf : (leibnizO _))]} ∗
  ⌜length conf > 0⌝.
Definition config_unset γ (cn:u64) : iProp Σ :=
  own γ.(pb_config_gn) {[cn := to_dfrac_agree (DfracOwn 1) ([] : (leibnizO _))]}.

Definition committed_by γ epoch σ : iProp Σ :=
  ∃ conf, is_epoch_config γ epoch conf ∗
      ∀ γ, ⌜γ ∈ conf⌝ → is_accepted_lb γ epoch σ.

Definition old_proposal_max γ epoch σ : iProp Σ := (* persistent *)
  □(∀ epoch_old σ_old,
   ⌜int.nat epoch_old < int.nat epoch⌝ →
   committed_by γ epoch_old σ_old → ⌜σ_old ⪯ σ⌝).

Definition pbN := nroot .@ "pb".
Definition sysN := pbN .@ "sys".
Definition opN := pbN .@ "op".

Definition is_valid_inv γ σ op : iProp Σ :=
  inv opN (
    (|={⊤∖↑pbN,∅}=> ∃ someσ, own_ghost γ someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γ (someσ ++ [op]) ={∅,⊤∖↑pbN}=∗ True)) ∨
    is_ghost_lb γ (σ ++ [op])
  )
.

Definition is_proposal_valid_old γ σ : iProp Σ :=
  ∀ σprev op σnext,
  ⌜σ = σprev ++ [op] ++ σnext⌝ -∗
  is_valid_inv γ σprev op.

Definition is_proposal_valid γ σ : iProp Σ :=
  □(∀ σ', ⌜σ' ⪯ σ⌝ → own_commit γ σ' ={⊤∖↑sysN}=∗ own_commit γ σ).

Definition is_proposal_facts γ epoch σ: iProp Σ :=
  old_proposal_max γ epoch σ ∗
  is_proposal_valid γ σ.

Definition own_Server_ghost γ epoch σ : iProp Σ :=
  "Hepoch_ghost" ∷ own_epoch γ epoch ∗
  "Haccepted" ∷ own_accepted γ epoch σ ∗
  "Haccepted_rest" ∷ ([∗ set] e' ∈ (fin_to_set u64), ⌜int.nat e' ≤ int.nat epoch⌝ ∨
                                                      own_accepted γ e' []) ∗
  "#Hproposal_lb" ∷ is_proposal_lb γ epoch σ ∗
  "#Hvalid" ∷ is_proposal_facts γ epoch σ
.

Lemma ghost_accept γ epoch epoch' σ σ' :
  int.nat epoch ≤ int.nat epoch' →
  σ ⪯ σ' →
  own_Server_ghost γ epoch σ -∗
  is_proposal_lb γ epoch' σ' -∗
  is_proposal_facts γ epoch' σ'
  ==∗
  own_Server_ghost γ epoch' σ'.
Proof.
  intros Hepoch_ineq Hσ_ineq.
  iIntros "Hown #Hprop_lb #Hprop_facts".
  iNamed "Hown".
  destruct (decide (epoch = epoch')).
  {
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

Lemma ghost_propose γ epoch σ op :
  own_proposal γ epoch σ -∗
  is_proposal_facts γ epoch σ -∗
  (|={⊤∖↑pbN,∅}=> ∃ someσ, own_ghost γ someσ ∗ (⌜someσ = σ⌝ -∗ own_ghost γ (someσ ++ [op]) ={∅,⊤∖↑pbN}=∗ True))
  ={⊤}=∗
  own_proposal γ epoch (σ ++ [op]) ∗
  (▷ is_proposal_facts γ epoch (σ ++ [op])).
Proof.
  iIntros "Hprop #Hprop_facts Hupd".
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
    iModIntro.
    iIntros.
    iAssert (⌜σ_old ⪯ σ⌝)%I as "%Hprefix".
    {
      iApply "Hmax".
      {
        done.
      }
      iFrame "#".
    }
    iPureIntro.
    apply prefix_app_r.
    done.
  }
  iDestruct "Hprop_facts" as "[_ #Hvalid]".
  unfold is_proposal_valid.

  iAssert (|={⊤}=> is_valid_inv γ σ op)%I with "[Hupd]" as ">#Hinv".
  {
    iMod (inv_alloc with "[Hupd]") as "$".
    {
      iNext.
      iFrame "Hupd".
    }
    done.
  }
  (* prove is_proposal_valid γ (σ ++ [op]) *)
  iModIntro.
  iModIntro.
  iModIntro.
  iIntros (σ') "%Hσ' Hσ'".
  assert (σ' ⪯ σ ∨ σ' = (σ ++ [op])) as [Hprefix_old|Hlatest].
  { (* TODO: list_solver. *)
    Search prefix.
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
    iAssert (|={⊤ ∖ ↑pbN,∅}=>
                ∃ someσ : list EntryType, own_ghost γ someσ ∗
                  (⌜someσ = σ⌝ -∗ own_ghost γ (someσ ++ [op]) ={∅,⊤ ∖ ↑pbN}=∗ True))%I
            with "[Hupd]" as "Hupd".
    { (* FIXME: need to strip off this later *)
      admit.
    }
    iMod (fupd_mask_subseteq (⊤∖↑pbN)) as "Hmask".
    {
      assert ((↑sysN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      assert ((↑opN:coPset) ⊆ (↑pbN:coPset)).
      { apply nclose_subseteq. }
      set_solver.
    }
    iMod "Hupd".
    iDestruct "Hupd" as (?) "[Hghost Hupd]".
    iDestruct (own_valid_2 with "Hghost Hσ") as %Hvalid.
    rewrite mono_list_auth_dfrac_op_valid_L in Hvalid.
    destruct Hvalid as [_ ->].
    iCombine "Hghost Hσ" as "Hσ".
    rewrite -mono_list_auth_dfrac_op.
    rewrite dfrac_op_own.
    rewrite Qp_half_half.
    iMod (own_update with "Hσ") as "Hσ".
    {
      apply (mono_list_update (σ ++ [op] : list (leibnizO EntryType))).
      by apply prefix_app_r.
    }
    iEval (rewrite -Qp_half_half) in "Hσ".
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
Admitted.

Definition sys_inv γ := inv sysN
(
  ∃ σ epoch,
  own_commit γ σ ∗
  committed_by γ epoch σ ∗
  is_proposal_lb γ epoch σ ∗
  is_proposal_facts γ epoch σ
).

(*
  User will get their (Q) by knowing (is_ghost_lb γ σ) where (op, Q) ∈ σ.
 *)
Lemma ghost_commit γ epoch σ :
  sys_inv γ -∗
  committed_by γ epoch σ -∗
  is_proposal_lb γ epoch σ -∗
  is_proposal_facts γ epoch σ
  ={⊤}=∗
  is_ghost_lb γ σ.
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

End pb_protocol.

Section pb_definitions.

Context `{!heapGS Σ, !stagedG Σ}.
Context `{!pbG Σ}.

Definition is_ApplyFn (applyFn:val) γ P : iProp Σ :=
  ∀ op_sl (epoch:u64) σ op,
  {{{
        (own_Server_ghost γ epoch σ ={⊤}=∗ own_Server_ghost γ epoch (σ++[op])) ∗
        crash_borrow (own_Server_ghost γ epoch σ ∗ P epoch σ) (
          ∃ epoch' σ',
          (own_Server_ghost γ epoch' σ' ∗ P epoch' σ')
        )
        ∗ is_slice op_sl byteT 1 op
  }}}
    applyFn (slice_val op_sl)
  {{{
        RET #();
        crash_borrow (own_Server_ghost γ epoch (σ ++ [op]) ∗ P epoch (σ ++ [op])) (
          ∃ epoch' σ',
          (own_Server_ghost γ epoch' σ' ∗ P epoch' σ')
        )
  }}}
.

Definition is_StateMachine (sm:loc) γ P : iProp Σ :=
  ∃ (applyFn:val),
  "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "Apply"] applyFn) ∗
  "#HapplySpec" ∷ is_ApplyFn applyFn γ P
.

Definition own_Server (s:loc) γ P : iProp Σ :=
  ∃ (epoch:u64) σ (nextIndex:u64) (isPrimary:bool) (sm:loc) (clerks:Slice.t),
  (* physical *)
  "Hepoch" ∷ s ↦[pb.Server :: "epoch"] #epoch ∗
  "HnextIndex" ∷ s ↦[pb.Server :: "nextIndex"] #nextIndex ∗
  "HisPrimary" ∷ s ↦[pb.Server :: "isPrimary"] #isPrimary ∗
  "Hsm" ∷ s ↦[pb.Server :: "sm"] #sm ∗
  "Hclerks" ∷ s ↦[pb.Server :: "clerks"] (slice_val clerks) ∗

  (* state-machine *)
  "#HisSm" ∷ is_StateMachine sm γ P ∗

  (* ghost-state *)
  "Hstate" ∷ crash_borrow (own_Server_ghost γ epoch σ ∗ P epoch σ) (
    ∃ epoch σ,
    own_Server_ghost γ epoch σ ∗ P epoch σ
  ) ∗

  (* primary-only *)
  "#Hclerks_rpc" ∷ True
.

Definition is_Server (s:loc) γ : iProp Σ :=
  ∃ (mu:val) P,
  "#Hmu" ∷ readonly (s ↦[pb.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock pbN mu (own_Server s γ P).

Record ApplyArgsC :=
{
  epoch : u64 ;
  index : u64 ;
  op : list u8 ;
}.

Definition has_encoding_ApplyArgs (encoded:list u8) (args:ApplyArgsC) : Prop.
Admitted.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop.
Admitted.

Program Definition ApplyAsBackup_spec γ :=
  λ (encoded_args:list u8), λne (Φ : list u8 -d> iPropO Σ) ,
  (∃ args σ,
    ⌜has_encoding_ApplyArgs encoded_args args⌝ ∗
    ⌜length σ = int.nat args.(index)⌝ ∗
    ⌜last σ = Some args.(op)⌝ ∗
    is_proposal_lb γ args.(epoch) σ ∗
    (∀ error (reply:list u8),
        ⌜has_encoding_Error reply error⌝ -∗
        (if (decide (error = 0)) then is_accepted_lb γ args.(epoch) σ else True) -∗
        Φ reply)
    )%I
.
Next Obligation.
  solve_proper.
Defined.

Context `{!urpcregG Σ}.

Definition is_pb_host γ (host:chan) :=
  handler_spec γ.(urpc_gn) host (U64 0) (ApplyAsBackup_spec γ).

Definition is_Clerk (ck:loc) γ : iProp Σ :=
  ∃ (cl:loc) srv,
  "#Hcl" ∷ readonly (ck ↦[pb.Clerk :: "cl"] #cl) ∗
  "#Hcl_rpc"  ∷ is_uRPCClient cl srv ∗
  "#Hsrv" ∷ is_pb_host γ srv
.

Lemma wpc_Server__epochFence {stk} (s:loc) γ (currEpoch epoch:u64) :
  {{{
        is_epoch_lb γ epoch ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗
        own_epoch γ currEpoch
  }}}
    pb.Server__epochFence #s #epoch @ stk
  {{{
        RET #(bool_decide (int.nat currEpoch > int.nat epoch));
        ⌜int.nat currEpoch ≥ int.nat epoch⌝ ∗
        s ↦[pb.Server :: "epoch"] #currEpoch ∗ own_epoch γ currEpoch
  }}}
  {{{
        own_epoch γ currEpoch
  }}}
.
Proof.
Admitted.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ (epoch index:u64) (op:list u8) op_sl :
  is_Server s γ -∗
  {{{
        "HargEpoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #epoch ∗
        "HargIndex" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #index ∗
        "HargOp" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
        "HopSl" ∷ is_slice op_sl byteT 1 op ∗
        "#HepochLb" ∷ is_epoch_lb γ epoch
  }}}
    pb.Server__ApplyAsBackup #s #args_ptr
  {{{
        RET #0; True
  }}}
  .
Proof.
  iIntros "#HisSrv" (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  Opaque crash_borrow.
  wp_loadField.
  wp_bind (Server__epochFence _ _).
  iApply (wpc_wp _ _ _ _ True).
  iApply (wpc_crash_borrow_open with "Hstate").
  {
    econstructor.
  }
  iSplitL ""; first done.
  iIntros "[Hghost HP]".
  unfold own_Server_ghost.
  iNamed "Hghost".
  wpc_apply (wpc_Server__epochFence with "[$Hepoch $Hepoch_ghost $HepochLb]").
  iSplit.
  {
    iIntros.
    iSplitL ""; first done.
    iExists _, _; iFrame "∗#".
  }
  iNext.
  iIntros "(%Hineq & Hepoch & $)".
  iFrame "Haccepted Haccepted_rest Hghost Hproposal_lb".
  iFrame "HP".
  iIntros "Hstate".
  iSplitL ""; first done.
  wp_if_destruct.
  { (* return error: stale *)
    admit.
  }
  replace (epoch0) with (epoch) by word.

  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* return errror: out-of-order *)
    admit.
  }

  wp_loadField.
  wp_loadField.
  iNamed "HisSm".
  wp_loadField.

  wp_apply ("HapplySpec" with "[$Hstate $HopSl]").
  { (* prove protocol step *)
    admit.
  }
  iIntros "Hstate".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (release_spec with "[$Hlocked $HmuInv HnextIndex HisPrimary Hsm Hclerks Hepoch Hstate]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    iFrame.
    iExists _; iFrame "#".
  }
  wp_pures.
  iApply "HΦ".
  done.
Admitted.

Implicit Type σ : list (list u8).
Implicit Type epoch : u64.

Definition replyFn σ (op:list u8) : (list u8).
Admitted.

Lemma wp_Server__Apply (s:loc) γ op_sl op Q :
  {{{
        is_Server s γ ∗
        is_slice op_sl byteT 1 op ∗
        (|={⊤,∅}=> ∃ σ, own_ghost γ σ ∗ (own_ghost γ (σ ++ [op]) ={∅,⊤}=∗ Q (replyFn σ op)))
  }}}
    pb.Server__Apply #s (slice_val op_sl)
  {{{
        reply_sl σ, RET (slice_val reply_sl);
        is_slice reply_sl byteT 1 (replyFn σ op) ∗
        (Q (replyFn σ op))
  }}}
  .
Proof.
  iIntros (Φ) "[#His Hpre] HΦ".
  iNamed "His".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_if_destruct.
  { (* return error "not primary" *)
    admit.
  }
  wp_loadField.
Admitted.

End pb_definitions.
