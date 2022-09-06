From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.

Section pb_getstate_proof.
Context `{!heapGS Σ, !stagedG Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
Notation has_op_encoding_injective := (pb_has_op_encoding_injective pb_record).
Notation compute_reply := (pb_compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

(* XXX: GetState doesn't actually *need* to do any epoch comparison.
   It could simply return the state it has and the epoch for which it is the state.
   The issue is that an old epoch would then be able to seal future epochs,
   which might hurt liveness.
 *)
(* FIXME: rename to GetStateAndSeal *)
Lemma wp_Clerk__GetState γ γsrv ck args_ptr (epoch_lb:u64) (epoch:u64) :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#Hghost_epoch_lb" ∷ is_epoch_lb γsrv epoch_lb ∗
        "Hargs" ∷ GetStateArgs.own args_ptr (GetStateArgs.mkC epoch)
  }}}
    Clerk__GetState #ck #args_ptr
  {{{
        (reply:loc) (err:u64), RET #reply;
        if (decide (err = U64 0)) then
            ∃ epochacc σ enc,
            ⌜int.nat epoch_lb ≤ int.nat epochacc⌝ ∗
            ⌜int.nat epochacc ≤ int.nat epoch⌝ ∗
            is_accepted_ro γsrv epochacc σ ∗
            is_proposal_facts γ epochacc σ ∗
            is_proposal_lb γ epochacc σ ∗
            GetStateReply.own reply (GetStateReply.mkC 0 (length σ) enc) ∗
            ⌜has_snap_encoding enc (fst <$> σ)⌝ ∗
            ⌜length σ = int.nat (U64 (length σ))⌝
          else
            GetStateReply.own reply (GetStateReply.mkC err 0 [])
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
  wp_apply (GetStateArgs.wp_Encode with "[$Hargs]").
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl & Hargs)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[_ [_ [$ _]]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold GetState_spec.
    iExists _, _.
    iSplitR; first done.
    simpl.
    unfold GetState_core_spec.
    iFrame "Hghost_epoch_lb".
    iSplit.
    { (* No error from RPC, state was returned *)
      iIntros (?????) "???".
      iIntros (??? Henc_reply) "Hargs_sl".
      iIntros (?) "Hrep Hrep_sl".
      wp_pures.
      wp_load.
      wp_apply (GetStateReply.wp_Decode with "[$Hrep_sl]").
      { done. }
      iIntros (reply_ptr) "Hreply".
      iIntros "HΦ".
      iApply ("HΦ" $! _ 0).
      iExists _, _, _.
      iFrame "Hreply".
      iSplitR; first done.
      iSplitR; first done.
      eauto with iFrame.
    }
    { (* GetState was rejected by the server (e.g. stale epoch number) *)
      iIntros (err) "%Herr_nz".
      iIntros.
      wp_pures.
      wp_load.
      wp_apply (GetStateReply.wp_Decode with "[-] []").
      { eauto. }
      iModIntro.
      iIntros (reply_ptr) "Hreply".

      iIntros "HΦ".
      iApply ("HΦ" $! _ err).
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
      wp_apply (wp_allocStruct).
      { repeat econstructor. apply zero_val_ty'. done. }
      iIntros (reply_ptr) "Hreply".
      iDestruct (struct_fields_split with "Hreply") as "HH".
      iNamed "HH".
      iIntros "HΦ".
      iApply ("HΦ" $! _ 3).
      iExists _. simpl. iFrame.
      replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done.
      iFrame.
      iApply is_slice_small_nil.
      done.
    }
    { exfalso. done. }
  }
Qed.

Lemma wp_Server__GetState γ γsrv s args_ptr args epoch_lb Φ :
  is_Server s γ γsrv -∗
  GetStateArgs.own args_ptr args -∗
  GetState_core_spec γ γsrv args.(GetStateArgs.epoch) epoch_lb (λ reply,
                                                          ∀ (reply_ptr:loc),
                                                          GetStateReply.own reply_ptr reply -∗
                                                          Φ #reply_ptr) -∗
  WP pb.Server__GetState #s #args_ptr {{ Φ }}
  .
Proof.
  iIntros "His_srv Hargs HΦ".
  wp_call.
  iNamed "His_srv".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  iNamed "Hargs".
  wp_loadField.

  (* FIXME: separate lemma; no-op spec for isEpochStale *)
  wp_call.
  wp_loadField.
  wp_if_destruct.
  { (* *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists  _, _, _, _, _, _, _.
      iFrame "∗#%".
    }
    unfold GetState_core_spec.
    iDestruct "HΦ" as "[_ HΦ]".
    iRight in "HΦ".
    wp_pures.
    wp_apply (wp_allocStruct).
    { Transparent slice.T. repeat econstructor.
      Opaque slice.T. }
    iIntros (reply_ptr) "Hreply".
    iDestruct (struct_fields_split with "Hreply") as "HH".
    iNamed "HH".
    iApply "HΦ"; last first.
    {
      iExists _. iFrame.
      replace (slice.nil) with (slice_val Slice.nil) by done.
      iFrame.
      simpl.
      iApply is_slice_small_nil.
      done.
    }
    simpl.
    done.
  }
  wp_storeField.
  wp_loadField.

  iAssert (_) with "HisSm" as "HisSm2".
  iNamed "HisSm2".
  wp_loadField.
  iDestruct "HΦ" as "[#Hepoch_lb HΦ]".
  wp_apply ("HgetStateSpec" with "[$Hstate]").
  {
    iIntros "Hghost".
    iDestruct "Hghost" as (?) "(%Heq & Hghost & Hprim)".
    iDestruct (ghost_helper1 with "Hs_prop_lb Hghost") as %Hσeq.
    {
      apply (f_equal length) in Heq.
      rewrite fmap_length in Heq.
      rewrite fmap_length in Heq.
      done.
    }
    rewrite Hσeq.
    iDestruct (ghost_epoch_lb_ineq with "Hepoch_lb Hghost") as "#Hepoch_ineq".
    iMod (ghost_seal with "Hghost") as "Hghost".
    iDestruct (ghost_get_accepted_ro with "Hghost") as "#Hacc_ro".
    replace (σ) with (σg).
    iSplitL "Hghost Hprim".
    {
      iExists _.
      iFrame.
      iPureIntro. done.
    }
    iModIntro.

    iCombine "Hacc_ro Hepoch_ineq" as "HH".
    iExact "HH".
  }
  iIntros (??) "(Hsnap_sl & %Hsnap_enc & [Hstate HQ])".
  iDestruct "HQ" as "[#Hacc_ro %Hineq]".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.

  iLeft in "HΦ".
  iDestruct ("HΦ" with "[% //] [%] Hacc_ro Hs_prop_facts Hs_prop_lb [%//] [%]") as "HΦ".
  { word. }
  { word. }

  wp_apply (release_spec with "[-Hsnap_sl HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists  _, _, _, _, _, _, _.
    iFrame "∗ HisSm #%".
  }
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.
    Opaque slice.T. }
  iIntros (reply_ptr) "Hreply".
  iDestruct (struct_fields_split with "Hreply") as "HH".
  iNamed "HH".
  iApply "HΦ".
  iExists _.
  iFrame.
  simpl.
  rewrite Hσ_nextIndex.
  replace (U64 (int.nat nextIndex)) with (nextIndex) by word.
  iFrame.
Qed.

End pb_getstate_proof.
