From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Import pb_ghost.
From Perennial.goose_lang.lib Require Import waitgroup.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_apply_proof.

Context `{!heapGS Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

(* Clerk specs *)
Lemma wp_Clerk__ApplyAsBackup γ γsrv ck args_ptr (epoch index:u64) σ ghost_op op_sl op :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗

        "#HepochLb" ∷ is_epoch_lb γsrv epoch ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Hghost_op_σ" ∷ ⌜last σ = Some ghost_op⌝ ∗
        "%Hghost_op_op" ∷ ⌜has_op_encoding op ghost_op.1⌝ ∗
        "%Hσ_index" ∷ ⌜length σ = ((int.nat index) + 1)%nat⌝ ∗
        "%HnoOverflow" ∷ ⌜int.nat index < int.nat (word.add index 1)⌝ ∗

        "#HargEpoch" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #epoch) ∗
        "#HargIndex" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #index) ∗
        "#HargOp" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl)) ∗
        "#HopSl" ∷ readonly (is_slice_small op_sl byteT 1 op)
  }}}
    Clerk__ApplyAsBackup #ck #args_ptr
  {{{
        (err:u64), RET #err; □ if (decide (err = 0)) then
                               is_accepted_lb γsrv epoch σ
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
    iExists _, _, _, _.
    iSplitR; first done.
    iFrame "#%".
    iSplitR; first iPureIntro.
    {
      instantiate (1:=ghost_op.2).
      rewrite Hghost_op_σ.
      destruct ghost_op.
      done.
    }
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

Lemma wp_Server__ApplyAsBackup (s:loc) (args_ptr:loc) γ γsrv args σ op Q Φ Ψ :
  is_Server s γ γsrv -∗
  ApplyAsBackupArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  ApplyAsBackup_core_spec γ γsrv args σ op Q Ψ -∗
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
      { iPureIntro. destruct sealed; naive_solver. }
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
      iFrame.
      iSplitR; first done.
      iModIntro.
      iApply to_named.
      do 9 (iExists _).
      iFrame "∗#%".
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
        do 9 (iExists _).
        iFrame "∗#%".
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
      do 9 (iExists _).
      iFrame "∗#%".
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
      do 9 (iExists _).
      iFrame "∗#%".
    }
    wp_pures.
    iRight in "HΨ".
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }
  replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* return error: out-of-order; TODO: we never actually need to return this
       error, if something is out of order that means we already applied it *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "Hlocked HmuInv".
      iNext.
      do 9 (iExists _).
      iFrame "Hepoch HnextIndex ∗ # %".
    }
    wp_pures.
    iApply "HΦ".
    iRight in "HΨ".
    iApply "HΨ".
    done.
  }

  wp_loadField.
  wp_loadField.
  wp_pures.

  iNamed "HisSm".
  wp_loadField.

  iMod (readonly_alloc_1 with "Hargs_op_sl") as "Hargs_op_sl".
  wp_apply ("HapplySpec" with "[$Hstate $Hargs_op_sl]").
  { (* prove protocol step *)
    iSplitL ""; first done.
    iIntros "Hghost".
    iDestruct "Hghost" as (?) "(%Hre & Hghost & Hprim)".
    iDestruct (ghost_accept_helper with "Hprop_lb Hghost") as "[Hghost %Happend]".
    {
      apply (f_equal length) in Hre.
      rewrite Hσ_nextIndex in Hre.
      rewrite Hre in Hσ_index.
      rewrite fmap_length in Hσ_index.
      word.
    }
    { done. }
    iMod (ghost_accept with "Hghost Hprop_lb Hprop_facts") as "Hghost".
    { done. }
    {
      rewrite Happend.
      rewrite app_length.
      word.
    }
    iMod (ghost_primary_accept with "Hprop_facts Hprop_lb Hprim") as "Hprim".
    {
      rewrite Happend.
      rewrite app_length.
      word.
    }
    rewrite Happend.
    iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
    iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb2".
    instantiate (1:=(is_epoch_lb γsrv epoch ∗ is_accepted_lb γsrv epoch σ)%I).
    iModIntro.

    iSplitL.
    { iExists _; iFrame "Hghost".
      iFrame "Hprim".
      rewrite fmap_snoc.
      by rewrite Hre. }
    replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
    iFrame "#".
  }
  iIntros (reply q waitFn) "(Hreply & Hstate & HwaitSpec)".
  wp_pures.
  wp_loadField.
  wp_storeField.
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
  wp_apply (release_spec with "[-HΨ HΦ HwaitSpec]").
  {
    iFrame "Hlocked HmuInv".
    iNext.
    do 9 (iExists _).
    replace ([op]) with ([(op, Q).1]) by done.
    iFrame "Hstate ∗#".
    iSplitR.
    { iExists _, _, _; iFrame "#". }
    iPureIntro.
    rewrite app_length.
    rewrite Hσ_nextIndex.
    simpl.
    word.
  }
  wp_pures.
  wp_apply "HwaitSpec".
  iIntros "#Hlb".
  wp_pures.

  iLeft in "HΨ".
  iApply "HΦ".
  iApply "HΨ".
  replace (epoch) with (args.(ApplyAsBackupArgs.epoch)) by word.
  iDestruct "Hlb" as "(_ & $)".
  done.
Qed.

End pb_apply_proof.
