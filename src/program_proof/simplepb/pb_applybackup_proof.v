From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
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
Context {pb_record:Sm.t}.
Notation OpType := (pb_record.(Sm.OpType)).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation "server.t" := (server.t (pb_record:=pb_record)).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation get_rwops := (get_rwops (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma is_StateMachine_acc_apply sm own_StateMachine P :
  is_StateMachine sm own_StateMachine P -∗
  (∃ applyFn,
    "#Happly" ∷ readonly (sm ↦[pb.StateMachine :: "StartApply"] applyFn) ∗
    "#HapplySpec" ∷ is_ApplyFn (pb_record:=pb_record) own_StateMachine applyFn P
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
        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch opsfull ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch opsfull ∗
        "%Hghost_op_σ" ∷ ⌜∃ γ, last opsfull = Some (rw_op op, γ)⌝ ∗
        "%Hghost_op_op" ∷ ⌜has_op_encoding op_bytes op⌝ ∗
        "%Hσ_index" ∷ ⌜length (get_rwops opsfull) = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op_bytes)
  }}}
    Clerk__ApplyAsBackup #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch opsfull
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
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_host_unfold.
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

Lemma primary_lb st γ γeph γsrv opsfull' sealed:
  is_proposal_lb γ st.(server.epoch) opsfull' -∗
  is_Primary_ghost_f γ γeph γsrv st -∗
  own_Server_ghost_f γ γsrv γeph st.(server.epoch) (get_rwops st.(server.ops_full_eph)) sealed -∗
  ⌜prefix (get_rwops opsfull') (get_rwops st.(server.ops_full_eph))⌝.
Proof.
  iIntros "#Hprop_lb #Hprim2 Hghost".
  iNamed "Hghost".
  iEval (rewrite /is_Primary_ghost_f /tc_opaque) in "Hprim2".
  iNamed "Hprim2".
  iNamed "Hghost".
  iDestruct (ghost_propose_lb_valid with "Htok_used_witness Hprim Hprop_lb") as %Hvalid.
  rewrite Hre. iPureIntro. by apply get_rwops_prefix.
Qed.

(* increase epheeral proposal on backup servers when getting new ops *)
(* The important part of this lemma is
   own_Server_ghost_eph_f st -∗ own_Server_ghost_eph_f st' *)
Lemma applybackup_eph sm st γ γsrv γeph ops_full_eph' {own_StateMachine} :
  st.(server.sealed) = false →
  length (get_rwops st.(server.ops_full_eph)) < length (get_rwops ops_full_eph') →
  is_StateMachine sm own_StateMachine (own_Server_ghost_f γ γsrv γeph) -∗
  is_proposal_lb γ st.(server.epoch) ops_full_eph' -∗
  is_proposal_facts γ st.(server.epoch) ops_full_eph' -∗
  £ 1 -∗
  own_Server_ghost_eph_f st γ γsrv γeph -∗
  own_StateMachine st.(server.epoch) (get_rwops st.(server.ops_full_eph)) false (own_Server_ghost_f γ γsrv γeph)
  -∗
  |NC={⊤,⊤}=> wpc_nval ⊤ (
                (own_StateMachine st.(server.epoch) (get_rwops (st.(server.ops_full_eph))) false (own_Server_ghost_f γ γsrv γeph)) ∗
                is_ephemeral_proposal_lb γeph st.(server.epoch) ops_full_eph' ∗
                own_Server_ghost_eph_f (st <|server.ops_full_eph := ops_full_eph'|>) γ γsrv γeph ∗
                ⌜ prefix st.(server.ops_full_eph) ops_full_eph' ⌝ ∗
                ⌜ st.(server.isPrimary) = false ⌝)
.
Proof.
  intros Hunsealed Hlen.
  iIntros "#HisSm #Hprop_lb #Hprop_facts Hlc HghostEph Hstate".
  iEval (rewrite /is_StateMachine /tc_opaque) in "HisSm".
  iNamed "HisSm".
  iEval (rewrite /own_Server_ghost_eph_f /tc_opaque) in "HghostEph".
  iNamed "HghostEph".

  iDestruct "Heph_prop_lb" as "#Heph_prop_lb".
  (* Want to establish:
     is_ephemeral_proposal_lb γeph args.(ApplyAsBackupArgs.epoch) opsfull
     This requires us to know that opsfull_ephemeral ⪯ opsfull.
     We will establish this using accP.
   *)
  rewrite Hunsealed.
  destruct st.(server.isPrimary) as [] eqn:HisPrimary.
  { (* case: is primary. *)
    iAssert (_) with "HprimaryOnly" as "Hprim2".
    iMod ("HaccP" with "Hlc [Heph] Hstate") as "$"; last first.
    { done. }
    iIntros (???) "Hghost".
    iNamed "Hghost".
    iNamed "Hghost".
    iEval (rewrite /is_Primary_ghost_f /tc_opaque) in "Hprim2".
    iDestruct "Hprim2" as "[%Hbad|Hprim2]"; first by exfalso.
    iNamed "Hprim2".
    iDestruct (ghost_propose_lb_valid with "Htok_used_witness Hprim Hprop_lb") as %Hvalid.
    iDestruct (own_valid_2 with "Heph Heph_lb") as %Hvalid2.
    exfalso.

    apply get_rwops_prefix in Hvalid.
    apply prefix_length in Hvalid.
    rewrite singleton_op singleton_valid in Hvalid2.
    apply mono_list_both_dfrac_valid_L in Hvalid2.
    destruct Hvalid2 as [_ Hvalid2].
    apply get_rwops_prefix in Hvalid2.
    apply prefix_length in Hvalid2.
    word.
  }
  { (* case: not primary *)
    iDestruct (own_valid_2 with "Heph_prop_lb Hprop_lb") as %Hcomp.
    rewrite singleton_op singleton_valid in Hcomp.
    rewrite csum.Cinr_valid in Hcomp.
    apply mono_list_lb_op_valid_L in Hcomp.
    destruct Hcomp as [Hprefix|Hprefix].
    2:{ (* case: opsfull_ephemeral ⪯ opsfull; no need to do any update at all *)
      exfalso.
      apply get_rwops_prefix, prefix_length in Hprefix.
      word.
    }
    {
      iMod (own_update with "Heph") as "Heph".
      {
        apply singleton_update.
        apply mono_list_update.
        exact Hprefix.
      }
      iDestruct (own_mono _ _ {[ _ := ◯ML _ ]} with "Heph") as "#Heph_lb".
      {
        apply singleton_mono.
        apply mono_list_included.
      }
      iModIntro.
      iApply wpc_nval_intro.
      iNext.
      iFrame "Hstate".
      iSplitL; last done.
      repeat iExists _.
      rewrite Hunsealed.
      iFrame "∗#".
      rewrite HisPrimary.
      simpl.
      iSplitR.
      { iModIntro; iFrame "#". }
      iSplitR.
      { iDestruct "Hprop_facts" as "(?&?&?)". iFrame "#". }
      iFrame "%".
      by iLeft.
    }
  }
Qed.

Lemma applybackup_step_helper (opsfull opsfull_old: list (GhostOpType * gname)) :
  (prefix opsfull opsfull_old ∨ prefix opsfull_old opsfull) →
  length (get_rwops opsfull) = length (get_rwops opsfull_old) + 1 →
  prefix opsfull_old opsfull.
Proof.
  intros [Hbad|Hgood]; last done.
  intros Hlen.
  exfalso.
  apply get_rwops_prefix, prefix_length in Hbad.
  lia.
Qed.


Lemma applybackup_step_helper2 (ops_full ops_full':list (GhostOpType * gname)) op a :
  last ops_full' = Some (rw_op op, a) →
  length (get_rwops ops_full') = length (get_rwops ops_full) + 1 →
  ops_full `prefix_of` ops_full' →
  get_rwops ops_full' = get_rwops ops_full ++ [op].
Proof.
Admitted.

Lemma applybackup_step γ γsrv γeph epoch ops ops_full' op a:
  last ops_full' = Some (rw_op op, a) →
  length (get_rwops ops_full') = length ops + 1 →
  is_proposal_lb γ epoch ops_full' -∗
  is_proposal_facts γ epoch ops_full' -∗
  is_ephemeral_proposal_lb γeph epoch ops_full' -∗
  own_Server_ghost_f γ γsrv γeph epoch ops false ={↑pbN}=∗
  own_Server_ghost_f γ γsrv γeph epoch (get_rwops ops_full') false ∗
  ⌜get_rwops ops_full' = ops ++ [op]⌝ ∗
  (is_epoch_lb γsrv epoch ∗ is_accepted_lb γsrv epoch ops_full')
.
Proof.
  intros Hlast Hlen.
  iIntros "#Hprop_lb #Hprop_facts #Heph_prop_lb Hown".
  iNamed "Hown".
  rename opsfull into ops_full.
  subst.

  (* deal with implicitly accepting RO ops *)
  iDestruct (ghost_accept_helper2 with "Hprop_lb Hghost") as "[Hghost %Hcomp]".
  epose proof (applybackup_step_helper _ _ Hcomp Hlen) as H.
  iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
  { done. }
  { by apply prefix_length. }
  iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
  { by apply prefix_length. }
  iModIntro.

  iDestruct (ghost_get_accepted_lb with "Hghost") as "#$".
  iDestruct (ghost_get_epoch_lb with "Hghost") as "#$".
  iSplitL.
  2:{ iPureIntro. by eapply applybackup_step_helper2. }
  iExists _; iFrame "Hghost Hprim #". done.
Qed.

Lemma increase_durableNextIndex st γ γsrv γeph ops_durable_full newDurableNextIndex:
  length (get_rwops ops_durable_full) = int.nat newDurableNextIndex →
  is_accepted_lb γsrv st.(server.epoch) ops_durable_full -∗
  own_Server_ghost_eph_f st γ γsrv γeph -∗
  own_Server_ghost_eph_f (st <| server.durableNextIndex:= newDurableNextIndex |>) γ γsrv γeph
.
Proof.
  intros. iIntros "?".
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed 1. iExists _; iFrame "∗#"; done.
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
  wp_bind (If (_ > _) _ _).
  wp_apply (wp_wand with "[Hargs_index HnextIndex Hargs_epoch Hepoch]").
  {
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    {
      wp_loadField.
      wp_loadField.
      wp_pures.
      iModIntro.
      instantiate (1:=(λ v, ("%Hisbool" ∷ ⌜v = #true ∨ v = #false⌝ ∗ _))%I).
      simpl.
      iSplitR.
      { iPureIntro. destruct bool_decide; naive_solver. }
      iNamedAccu.
    }
    {
      iFrame.
      iPureIntro.
      by right.
    }
  }
  iIntros (?).
  iNamed 1.
  wp_bind (If v _ #false).
  wp_apply (wp_wand with "[Hsealed]").
  {
    wp_pures.
    destruct Hisbool as [-> | ->].
    {
      wp_pures.
      wp_loadField.
      wp_pures.
      instantiate (1:=(λ w, ("%Hisboolw" ∷ ⌜w = #true ∨ w = #false⌝ ∗ _))%I).
      simpl.
      iModIntro.
      iSplitR.
      { iPureIntro. destruct st.(server.sealed); naive_solver. }
      iNamedAccu.
    }
    {
      wp_pures.
      iSplitR.
      { iPureIntro. naive_solver. }
      by iFrame.
    }
  }

  iIntros (?).
  iNamed 1.
  wp_pures.
  destruct Hisboolw as [-> | ->].
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
      rewrite Heqb.
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
      rewrite Heqb.
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
      rewrite Heqb.
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

  iMod (applybackup_eph with "HisSm Hprop_lb Hprop_facts Hlc HghostEph Hstate") as "HH".
  { done. }
  {
    rewrite Hσ_index.
    rewrite Heqb1.
    (* FIXME: why do I need to rewrite these? *)
    word_cleanup.
    (* FIXME: don't want to manually unfold this *)
    unfold no_overflow in HnextIndexNoOverflow.
    word.
  }

  wp_bind (struct.loadF _ _ _).
  wp_apply (wpc_nval_elim_wp with "HH").
  { done. }
  { done. }

  iDestruct (is_StateMachine_acc_apply with "HisSm") as "HH".
  iNamed "HH".
  wp_loadField.
  wp_pures.
  iIntros "(Hstate & HghostEph & %Heph_prefix & %HnotPrimary)".
  rewrite HnotPrimary.

  iMod (readonly_alloc_1 with "Hargs_op_sl") as "Hargs_op_sl".
  wp_apply ("HapplySpec" with "[$Hstate $Hargs_op_sl]").
  {
    iSplitL; first done.
    iIntros "Hghost".
    iMod (applybackup_step with "Hprop_lb Hprop_facts [] Hghost") as "Hghost".
    { done. }
    { admit. }
    { admit. } (* FIXME: get eph_lb *)
    iModIntro.
    iDestruct "Hghost" as "(Hghost & %Hre & H)".
    rewrite Hre.
    iFrame "Hghost".
    iAccu.
  }

  iIntros (reply q waitFn) "(Hreply & Hstate & HwaitSpec)".
  epose proof (applybackup_step_helper2 _ _ _ _ Hghost_op_σ _ Heph_prefix) as Hre.
  Unshelve.
  2:{ rewrite Hσ_index. unfold no_overflow in HnextIndexNoOverflow.
      rewrite Heqb1. word. }
  rewrite -Hre.

  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HopAppliedConds_map").
  iIntros (cond ok) "[%Hlookup HopAppliedConds_map]".
  wp_pures.
  wp_bind (If _ _ _).
  wp_apply (wp_wand with "[HopAppliedConds_map HopAppliedConds HnextIndex]").
  {
    wp_if_destruct.
    { (* map lookup succeeded, signal the condvar *)
      apply map_get_true in Hlookup.
      iDestruct (big_sepM_lookup_acc with "HopAppliedConds_conds") as "[Hiscond _]".
      { done. }
      wp_apply (wp_condSignal with "Hiscond").
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapDelete with "HopAppliedConds_map").
      iIntros "HopAppliedConds_map".
      simpl.
      iAssert (∃ newOpAppliedConds,
                  is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                  [∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu
              )%I with "[HopAppliedConds_map]" as "H".
      {
        iExists _; iFrame.
        unfold map_del.
        iDestruct (big_sepM_delete with "HopAppliedConds_conds") as "[_ $]".
        { done. }
      }
      (* FIXME: iNamedAccu and iAccu turn the strings into "^@^@^@^@^@..." *)
      instantiate (1:=(λ _, _)%I).
      (* iAccu. *)
      (* iNamedAccu. *)
      instantiate (1:=
                  (
        "HopAppliedConds" ∷ s ↦[Server :: "opAppliedConds"] #opAppliedConds_loc ∗
        "HnextIndex" ∷ s ↦[Server :: "nextIndex"] #_ ∗
        "H" ∷ ∃ newOpAppliedConds, (is_map opAppliedConds_loc 1 newOpAppliedConds ∗
                ([∗ map] cond0 ∈ newOpAppliedConds, is_cond cond0 mu))
                )%I
      ).
      iAccu.
    }
    { (* FIXME: What are those weird ^@? *)
      simpl.
      iModIntro.
      iFrame.
      iExists _; iFrame "∗#".
    }
  }
  iIntros (?).
  iNamed 1.
  iDestruct "H" as (?) "[HopAppliedConds_map #HopAppliedConds_conds2]".
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
    rewrite HnotPrimary Heqb.
    iFrame "∗".
    iSplitL "HnextIndex".
    {
      rewrite Hre.
      rewrite app_length /=.
      iApply to_named.
      iExactEq "HnextIndex".
      repeat f_equal.
      unfold no_overflow in HnextIndexNoOverflow.
      rewrite -Heqb1.
      admit. (* TODO: overflow reasoning *)
    }
    iFrame "#".
    iPureIntro.
    unfold no_overflow.
    word.
  }

  wp_pures.
  wp_apply "HwaitSpec".
  iIntros "#Hlb".
  wp_pures.

  (* possibly update durableNextIndex *)
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iClear "HopAppliedConds_conds HdurableNextIndex_is_cond HroOpsToPropose_is_cond".
  iClear "HcommittedNextRoIndex_is_cond HisSm".
  (* FIXME: why doesn't Hdurable_lb get automatically get destructed into Hdurable_lb2? *)

  wp_pures.
  wp_bind  ((if: (if: _ then _ else _) then _ else _)%E).
  wp_apply (wp_wand with "[Hown Hargs_epoch]").
  {
    instantiate (1:= λ _, mu_inv s γ γsrv mu).
    iNamed "Hown".
    iNamed "Hvol".
    wp_bind (if: struct.loadF _ _ _ = _ then _ else _)%E.
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    {
      wp_loadField.
      wp_if_destruct.
      { (* case: increase durableNextIndex *)
        iDestruct "Hlb" as "[_ Hlb]".
        replace (st.(server.epoch)) with (args.(ApplyAsBackupArgs.epoch)) by word.

        replace (args.(ApplyAsBackupArgs.epoch)) with (st0.(server.epoch)); last first.
        { rewrite -Heqb2. word. } (* FIXME: why do we need to manually rewrite? *)
        iDestruct (increase_durableNextIndex with "Hlb HghostEph") as "HghostEph".
        { instantiate (1:=(word.add args.(ApplyAsBackupArgs.index) 1)). word. }

        wp_storeField.
        rewrite Heqb1. (* to match up ApplyArgs.index and (length (rws ops_full_eph)) *)
        wp_loadField.
        wp_apply (wp_condBroadcast with "[]"); first iFrame "#".
        wp_pures.
        wp_loadField.
        wp_loadField.
        wp_bind ((if: #_ = #_ then _ else _)%E).
        wp_if_destruct.
        {
          wp_loadField.
          wp_loadField.
          wp_pures.
          wp_if_destruct.
          {
            wp_loadField.
            wp_apply (wp_condSignal with "[]"); first iFrame "#".
            repeat iExists _. iFrame "HghostEph".
            repeat iExists _. time (iFrame "∗ #"; iFrame "%").
          }
          {
            iModIntro.
            repeat iExists _. iFrame "HghostEph".
            repeat iExists _. time (iFrame "∗ #"; iFrame "%").
          }
        }
        wp_pures.
        iModIntro.
        repeat iExists _. iFrame "HghostEph".
        repeat iExists _. time (iFrame "∗ #"; iFrame "%").
      }
      {
        iModIntro.
        repeat iExists _. iFrame "HghostEph".
        repeat iExists _. time (iFrame "∗#"; iFrame "%").
      }
    }
    wp_pures.
    {
      iModIntro.
      repeat iExists _. iFrame "HghostEph".
      repeat iExists _. time (iFrame "∗#"; iFrame "%").
    }
  }

  iIntros (?) "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[$HmuInv $Hlocked $Hown]").
  wp_pures.

  iLeft in "HΨ".
  iApply "HΦ".
  iApply "HΨ".
  iDestruct "Hlb" as "(_ & $)".
  done.
Admitted.

End pb_applybackup_proof.
