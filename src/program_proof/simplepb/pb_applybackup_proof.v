From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_protocol.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_applybackup_proof.

Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.
Import Sm.

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma is_StateMachine_acc_apply sm own_StateMachine P :
  is_StateMachine sm own_StateMachine P -∗
  (∃ applyFn,
    "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "StartApply"] applyFn) ∗
    "#HapplySpec" ∷ is_ApplyFn own_StateMachine applyFn P
  )
.
Proof.
  rewrite /is_StateMachine /tc_opaque.
  iNamed 1. iExists _; iFrame "#".
Qed.

(* Clerk specs *)
Lemma wp_Clerk__ApplyAsBackup γ γsrv ck args_ptr (epoch index:u64) opsfull op op_sl op_bytes :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#HepochLb" ∷ is_epoch_lb γsrv.(r_pb) epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ.(s_pb) epoch opsfull ∗
        "#Hprop_facts" ∷ is_proposal_facts γ.(s_pb) epoch opsfull ∗
        "#Hprim_facts" ∷ is_proposal_facts_prim γ.(s_prim) epoch opsfull ∗
        "%Hghost_op_σ" ∷ ⌜∃ γ, last opsfull = Some (op, γ)⌝ ∗
        "%Hghost_op_op" ∷ ⌜has_op_encoding op_bytes op⌝ ∗
        "%Hσ_index" ∷ ⌜length (get_rwops opsfull) = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (own_slice_small op_sl byteT 1 op_bytes)
  }}}
    Clerk__ApplyAsBackup #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv.(r_pb) epoch opsfull
                             else True
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep) "Hrep".
  wp_pures.
  iNamed "Hck".
  wp_apply (ApplyAsBackupArgs.wp_Encode with "[]").
  {
    instantiate (1:=(ApplyAsBackupArgs.mkC _ _ _)).
    iExists _; iFrame "#".
  }
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl)".
  wp_loadField.
  iDestruct (own_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_rpcs_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[$ _]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold SetState_spec.
    destruct Hghost_op_σ as [? Hghost_op_σ].
    iExists _, _, _, _.
    iSplitR; first done.
    iFrame "#%".
    iSplit.
    { (* No error from RPC, Apply was accepted *)
      iIntros "#Hacc_lb".
      iIntros (?) "%Henc_rep Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.

      (* FIXME: separate lemma *)
      wp_call.
      rewrite Henc_rep.
      wp_apply (wp_ReadInt with "Hrep_sl").
      iIntros (?) "_".
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iModIntro.
      iFrame "#".
    }
    { (* Apply was rejected by the server (e.g. stale epoch number) *)
      iIntros (err) "%Herr_nz".
      iIntros.
      wp_pures.
      wp_load.
      wp_call.
      rewrite H.
      wp_apply (wp_ReadInt with "[$]").
      iIntros.
      wp_pures.
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      iFrame.
      iModIntro.
      destruct (decide _).
      {
        exfalso. done.
      }
      {
        done.
      }
    }
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      destruct (decide (_)).
      { exfalso. done. }
      { done. }
    }
    { exfalso. done. }
  }
Qed.

Lemma applybackup_primary_eph γ γsrv isPrimary canBecomePrimary epoch committedNextIndex opsfull ops_full_eph' :
  (length (get_rwops opsfull)) < (length (get_rwops ops_full_eph')) →
  is_proposal_lb γ.(s_pb) epoch opsfull -∗
  is_proposal_lb γ.(s_pb) epoch ops_full_eph' -∗
  is_proposal_facts γ.(s_pb) epoch ops_full_eph' -∗
  own_Primary_ghost_f γ γsrv canBecomePrimary isPrimary epoch committedNextIndex opsfull -∗
  ⌜prefix opsfull ops_full_eph'⌝ ∗
  own_Primary_ghost_f γ γsrv canBecomePrimary isPrimary epoch committedNextIndex ops_full_eph'

.
Proof.
  intros Hineq.
  rewrite /own_Primary_ghost_f /tc_opaque.
  iIntros "#Hs_prop_lb #Hprop_lb #Hprop_facts".
  iNamed 1.
  iFrame.
  destruct isPrimary.
  {
    iDestruct (ghost_propose_lb_valid with "Hprim Hprop_lb") as %Hbad.
    exfalso.
    apply prefix_length in Hbad.
    do 2 rewrite fmap_length in Hineq.
    lia.
  }

  iDestruct (fmlist_ptsto_lb_comparable with "Hprop_lb Hs_prop_lb") as %[Hbad|?].
  {
    exfalso.
    do 2 rewrite fmap_length in Hineq.
    apply prefix_length in Hbad.
    lia.
  }
  iFrame "%#".
  iSplitR; last done.
  by iApply is_proposal_facts_prim_mono.
Qed.

(* The important part of this lemma is
   own_Server_ghost_eph_f st -∗ own_Server_ghost_eph_f st' *)
Lemma applybackup_eph st γ γsrv ops_full_eph' :
  (length (get_rwops st.(server.ops_full_eph))) < (length (get_rwops ops_full_eph')) →
  is_proposal_lb γ.(s_pb) st.(server.epoch) ops_full_eph' -∗
  is_proposal_facts γ.(s_pb) st.(server.epoch) ops_full_eph' -∗
  own_Server_ghost_eph_f st γ γsrv -∗
  own_Server_ghost_eph_f (st <|server.ops_full_eph := ops_full_eph'|>) γ γsrv ∗
  ⌜prefix st.(server.ops_full_eph) ops_full_eph'⌝
.
Proof.
  intros Hlen.
  iIntros "#Hprop_lb #Hprop_facts HghostEph".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque) in "HghostEph".
  iNamed "HghostEph".
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iFrame "#".
  simpl.
  iDestruct (applybackup_primary_eph with "Hs_prop_lb Hprop_lb [$] Hprimary") as "[% $]".
  { lia. }
  iSplitR; last done.
  repeat iExists _.
  iFrame "#%".
Qed.

Lemma applybackup_step_helper (opsfull opsfull_old: list (OpType * gname)) :
  (prefix opsfull opsfull_old ∨ prefix opsfull_old opsfull) →
  length (get_rwops opsfull) = length (get_rwops opsfull_old) + 1 →
  prefix opsfull_old opsfull.
Proof.
  intros [Hbad|Hgood]; last done.
  intros Hlen.
  exfalso.
  apply prefix_length in Hbad.
  do 2 rewrite fmap_length in Hlen.
  lia.
Qed.

Lemma applybackup_step_helper2 (ops_full ops_full':list (OpType * gname)) op a :
  last ops_full' = Some (op, a) →
  length (get_rwops ops_full') = length (get_rwops ops_full) + 1 →
  ops_full `prefix_of` ops_full' →
  get_rwops ops_full' = get_rwops ops_full ++ [op].
Proof.
  intros.
  destruct H1 as [? ->].
  rewrite /get_rwops fmap_app.
  assert (length x = 1).
  {
    rewrite fmap_length app_length in H0.
    rewrite fmap_length in H0.
    lia.
  }
  destruct x.
  { by exfalso. }
  simpl. destruct x. 2: by exfalso.
  simpl.
  rewrite last_app /= in H.
  injection H as ?. subst.
  done.
Qed.

Lemma applybackup_step γ γsrv epoch ops ops_full' op a:
  last ops_full' = Some (op, a) →
  length (get_rwops ops_full') = length ops + 1 →
  is_proposal_lb γ.(s_pb) epoch ops_full' -∗
  is_proposal_facts γ.(s_pb) epoch ops_full' -∗
  is_proposal_facts_prim γ.(s_prim) epoch ops_full' -∗
  own_Server_ghost_f γ γsrv epoch ops false ={⊤∖↑pbAofN}=∗
  own_Server_ghost_f γ γsrv epoch (get_rwops ops_full') false ∗
  ⌜get_rwops ops_full' = ops ++ [op]⌝ ∗
  (is_epoch_lb γsrv.(r_pb) epoch ∗ is_accepted_lb γsrv.(r_pb) epoch ops_full')
.
Proof.
  intros Hlast Hlen.
  iIntros "#Hprop_lb #Hprop_facts #Hprim_facts_in Hown".
  iNamed "Hown".
  rename opsfull into ops_full.
  subst.

  (* deal with implicitly accepting RO ops *)
  iDestruct (ghost_accept_helper2 with "Hprop_lb Hghost") as "[Hghost %Hcomp]".
  epose proof (applybackup_step_helper _ _ Hcomp Hlen) as H.
  iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
  { done. }
  { by apply prefix_length. }
  iModIntro.

  iDestruct (ghost_get_accepted_lb with "Hghost") as "#$".
  iDestruct (ghost_get_epoch_lb with "Hghost") as "#$".
  iSplitL.
  2:{ iPureIntro. by eapply applybackup_step_helper2. }
  iExists _; iFrame "Hghost ∗". iFrame "#". done.
Qed.

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv args ops_full' op Q Φ Ψ :
  is_Server s γ γsrv -∗
  ApplyAsBackupArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  ApplyAsBackup_core_spec γ γsrv args ops_full' op Q Ψ -∗
  WP pb.Server__ApplyAsBackup #s #args_ptr {{ Φ }}
.
Proof.
  iIntros "#HisSrv Hpre HΦ HΨ".
  iNamed "Hpre".
  iNamed "HisSrv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  wp_pures.

  (* for loop to wait for previous op to be applied *)
  wp_bind (For _ _ _).
  wp_forBreak_cond.
  wp_pures.

  iNamed "Hown".
  iNamed "Hvol".

  wp_loadField.
  wp_bind ((_ > _) && _ && _)%E.
  wp_apply (wp_and2 with "[Hsealed Hargs_index HnextIndex Hargs_epoch Hepoch]"); first iNamedAccu; iNamed 1.
  { wp_loadField. wp_pures. iFrame. done. }
  { wp_loadField. wp_loadField. wp_pures. iFrame. done. }
  { wp_loadField. wp_pures. iFrame.
    instantiate (2:=(st.(server.sealed) = false)).
    iPureIntro.
    f_equal.
    (* FIXME: lemma for this? *)
    destruct st.
    simpl.
    destruct sealed.
    { by rewrite bool_decide_false. }
    { by rewrite bool_decide_true. }
  }
  Unshelve.
  2:{
    apply _.
  }
  wp_if_destruct.
  { (* loop again *)
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapGet with "HopAppliedConds_map").
    iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
    wp_pures.
    wp_if_destruct.
    { (* no condvar exists, let's make one *)
      wp_loadField.
      wp_apply (wp_newCond with "[$HmuInv]").
      apply map_get_false in Hlookup as [Hlookup _].
      clear dependent cond.
      iIntros (cond) "#Hiscond".
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapInsert with "HopAppliedConds_map").
      { done. }
      iIntros "HopAppliedConds_map".
      wp_pures.
      iLeft.

      (* PERF *)
      (* iFrame. is much slower than listing the specific hypotheses to frame *)
      iFrame "Hargs_op Hargs_op_sl Hargs_epoch Hargs_index HΨ HΦ Hlocked".
      iSplitR; first done.
      iModIntro.
      iApply to_named.
      repeat iExists _.

      (* Q: what about a tactic that looks for names in the goal, and iFrames those in order? *)
      (* PERF. The three iFrames is faster than one. *)
      (* time iFrame "∗#%". *)
      iFrame "HghostEph".

      (* establish own_Server *)
      repeat iExists _.
      time (iFrame "∗"; iFrame "#"; iFrame "%").

      unfold typed_map.map_insert.
      iDestruct (big_sepM_insert with "[$HopAppliedConds_conds]") as "$".
      { done. }
      { iFrame "#". }
    }
    { (* condvar exists, let's wait *)
      apply map_get_true in Hlookup.
      iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[His_cond _]".
      { done. }
      wp_apply (wp_condWait with "[-HΦ HΨ Hargs_op Hargs_op_sl Hargs_index Hargs_epoch]").
      {
        iFrame "His_cond".
        iFrame "HmuInv Hlocked".
        repeat (iExists _).
        iSplitR "HghostEph"; last iFrame "HghostEph".
        (* time iFrame "∗#%". *)
        repeat (iExists _).
        time (iFrame "∗"; iFrame "#"; iFrame "%").
      }
      iIntros "[Hlocked Hown]".
      wp_pures.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iFrame.
    }
  }
  (* done looping *)
  wp_pures.
  iModIntro.
  iRight.
  iSplitR; first done.
  wp_pures.

  iNamed "HΨ".
  wp_loadField.
  wp_if_destruct.
  { (* return error: sealed *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame "HghostEph".
      (* time iFrame "∗#%". *)
      repeat (iExists _).
      rewrite Heqb0.
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_apply (wp_Server__isEpochStale with "Hepoch").
  iIntros "Hepoch".
  wp_if_destruct.
  { (* return error: stale *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "Hlocked HmuInv".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame "HghostEph".
      (* time iFrame "∗#%". *)
      repeat (iExists _).
      rewrite Heqb0.
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iRight in "HΨ".
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }
  replace (args.(ApplyAsBackupArgs.epoch)) with st.(server.epoch) by word.
  wp_loadField.
  wp_loadField.
  wp_pure1_credit "Hlc".
  wp_if_destruct.
  { (* return error: out-of-order; TODO: we never actually need to return this
       error, if something is out of order that means we already applied it *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "Hlocked HmuInv".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame "HghostEph".
      (* time iFrame "∗#%". *)
      repeat (iExists _).
      rewrite Heqb0.
      iFrame "∗".
      time (iFrame "∗"; iFrame "#"; iFrame "%").
    }
    wp_pures.
    iApply "HΦ".
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_loadField.

  iDestruct (applybackup_eph with "Hprop_lb Hprop_facts HghostEph") as "[HghostEph %Hprefix]".
  { rewrite Hσ_index.
    rewrite Heqb2.
    unfold no_overflow in HnextIndexNoOverflow.
    word.
  }

  wp_bind (struct.loadF _ _ _).

  iDestruct (is_StateMachine_acc_apply with "HisSm") as "HH".
  iNamed "HH".
  wp_loadField.
  wp_pures.

  iMod (readonly_alloc_1 with "Hargs_op_sl") as "Hargs_op_sl".
  wp_apply ("HapplySpec" with "[$Hstate $Hargs_op_sl]").
  {
    iSplitL; first done.
    iIntros "_ Hghost".
    iMod (applybackup_step with "Hprop_lb Hprop_facts Hprim_facts Hghost") as "Hghost".
    { done. }
    {
      rewrite Hσ_index.
      f_equal.
      unfold no_overflow in HnextIndexNoOverflow.
      rewrite -HnextIndexNoOverflow.
      by rewrite Heqb2.
    } (* FIXME: why doesn't `word` work? *)
    iModIntro.
    iDestruct "Hghost" as "(Hghost & %Hre & H)".
    rewrite Hre.
    iFrame "Hghost".
    iAccu.
  }

  iIntros (reply q waitFn) "(_ & Hreply & Hstate & HwaitSpec)".

  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.

  wp_loadField.
  wp_apply (wp_MapGet with "HopAppliedConds_map").
  iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
  wp_pures.

  wp_apply (wp_If_join with "[HopAppliedConds HopAppliedConds_map HnextIndex]").
  {
    instantiate (1:=(∃ newOpAppliedConds,
                "HopAppliedConds_map" ∷ own_map opAppliedConds_loc 1 newOpAppliedConds ∗
                "#HopAppliedConds_conds" ∷ ([∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu) ∗
                "HopAppliedConds" ∷ s ↦[Server :: "opAppliedConds"] #opAppliedConds_loc ∗
                "HnextIndex" ∷ s ↦[Server :: "nextIndex"] #(_)
            )%I).
    (* FIXME: why can't I leave HopAppliedConds and HnextIndex as an evar
       without messing up the strings? *)
    iSplit.
    2:{
      iIntros (?). subst. wp_pures.
      iModIntro. iSplitR; first done.
      iExists _. iFrame "∗#".
    }
    iIntros (->).
    apply map_get_true in Hlookup.
    iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[Hiscond _]".
    { done. }
    wp_apply (wp_condSignal with "Hiscond").
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapDelete with "HopAppliedConds_map").
    iIntros "HopAppliedConds_map".
    iSplitR; first done.
    iExists _; iFrame "∗#".
    unfold map_del.
    iDestruct (big_sepM_delete with "HopAppliedConds_conds") as "[_ $]".
    { done. }
  }
  iClear "HopAppliedConds_conds".
  iNamed 1.
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[-HΨ HΦ HwaitSpec Hargs_epoch]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    repeat (iExists _).
    iSplitR "HghostEph"; last iFrame.

    repeat iExists _.
    simpl.
    rewrite Heqb0.
    iFrame "∗".
    iSplitL "HnextIndex".
    {
      rewrite Hσ_index.
      rewrite Heqb2.
      iApply to_named.
      iExactEq "HnextIndex".
      repeat f_equal.
      unfold no_overflow in HnextIndexNoOverflow.
      rewrite -Heqb2.
      word.
    }
    epose proof (applybackup_step_helper2 _ _ _ _ Hghost_op_σ _ Hprefix) as H.
    Unshelve.
    3: {
      unfold no_overflow in HnextIndexNoOverflow.
      rewrite Hσ_index.
      rewrite Heqb2.
      word. (* FIXME: why do I need to manually rewrite? *)
    }
    2: { shelve. }
    rewrite -H.
    iFrame.
    iFrame "HisSm #".
    iPureIntro.
    unfold no_overflow.
    word.
  }

  wp_pures.
  wp_apply "HwaitSpec".
  iIntros "#Hlb".
  wp_pures.

  iLeft in "HΨ".
  iApply "HΦ".
  iApply "HΨ".
  iDestruct "Hlb" as "(_ & $)".
  by iModIntro.
Qed.

End pb_applybackup_proof.
