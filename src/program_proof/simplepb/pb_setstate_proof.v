From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.

Section pb_setstate_proof.
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

Lemma wp_Clerk__SetState γ γsrv ck args_ptr (epoch:u64) σ snap :
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#Hprop_lb" ∷ is_proposal_lb γ epoch σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ epoch σ ∗
        "%Henc" ∷ ⌜has_snap_encoding snap (fst <$> σ)⌝ ∗
        "%Hno_overflow" ∷ ⌜length σ = int.nat (length σ)⌝ ∗
        "Hargs" ∷ SetStateArgs.own args_ptr (SetStateArgs.mkC epoch (length σ) snap)
  }}}
    Clerk__SetState #ck #args_ptr
  {{{
        (err:u64), RET #err;
        □(if (decide (err = U64 0)) then
            is_epoch_lb γsrv epoch
          else
            True)
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
  wp_apply (SetStateArgs.wp_Encode with "[$Hargs]").
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl & Hargs)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    iDestruct "Hsrv" as "[_ [$ _]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold SetState_spec.
    iExists _, _.
    iSplitR; first done.
    iSplitR; first done.
    simpl.
    iSplitR.
    { iPureIntro. done. }
    iFrame "Hprop_lb Hprop_facts".
    iSplit.
    { (* No error from RPC, state was accepted *)
      iIntros "#Hepoch_lb".
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
      iFrame "Hepoch_lb".
    }
    { (* SetState was rejected by the server (e.g. stale epoch number) *)
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

Lemma wp_Server__SetState γ γsrv s args_ptr args σ Φ :
  is_Server s γ γsrv -∗
  SetStateArgs.own args_ptr args -∗
  SetState_core_spec γ γsrv args σ (λ err, Φ #err) -∗
  WP pb.Server__SetState #s #args_ptr {{ Φ }}
  .
Proof.
  iIntros "#His_srv Hargs HΦ".
  iNamed "His_srv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iNamed "Hargs".
  wp_loadField.
  wp_loadField.
  wp_if_destruct.
  { (* stale epoch *)
    wp_loadField.
    unfold SetState_core_spec.
    iDestruct "HΦ" as "(_ & _ & _ & _ & HΦ)".
    iRight in "HΦ".
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    done.
  }
  { (* successfully set the state *)
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    { (* state has been set previously. Use is_prop_lb to get agreement. *)
      wp_loadField.

      iDestruct "HΦ" as "(_ & _ & _ & _ & HΦ)".
      iLeft in "HΦ".
      wp_apply (release_spec with "[-HΦ]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        iExists _, _, _, _, _, _, _.
        iFrame "∗#%".
      }
      wp_pures.
      iApply "HΦ".
      { iFrame "#". done. }
    }
    iAssert (_) with "HisSm" as "#HisSm2".
    iNamed "HisSm2".
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_loadField.

    iDestruct "HΦ" as "(%Henc_snap &  %Hlen_nooverflow & #Hprop_lb & #Hprop_facts & HΦ)".
    replace (args.(SetStateArgs.nextIndex)) with (U64 (length σ)) by word.
    replace (length σ) with (length σ.*1); last first.
    { by rewrite fmap_length. }

    wp_apply ("HsetStateSpec" with "[$Hstate]").
    {
      iSplitR; first done.
      iFrame "Hargs_state_sl".
      iIntros "Hghost".
      iDestruct "Hghost" as (?) "[%Heq Hghost]".
      iMod (ghost_accept_and_unseal with "Hghost Hprop_lb [$]") as "Hstate".
      {
        assert (int.nat epoch < int.nat args.(SetStateArgs.epoch) ∨
        int.nat epoch = int.nat args.(SetStateArgs.epoch) ∨
        (int.nat epoch > int.nat args.(SetStateArgs.epoch))) as [|[|]] by word.
        { word. }
        { exfalso. replace (epoch) with (args.(SetStateArgs.epoch)) in * by word.
          done. }
        { word. }
      }
      iDestruct (ghost_get_epoch_lb with "Hstate") as "#Hepoch_lb".
      iDestruct (ghost_get_accepted_lb with "Hstate") as "#Hacc_lb".
      iSplitL.
      {
        iExists _.
        iFrame.
        iPureIntro. done.
      }
      iModIntro.
      iCombine "Hepoch_lb Hacc_lb" as "HH".
      iExact "HH".
    }
    iIntros "(Hstate & #Hepoch_lb & #Hacc_lb)".
    wp_pures.
    wp_loadField.

    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "∗ HisSm #%".
      iPureIntro.
      rewrite fmap_length.
      word.
    }
    wp_pures.
    iLeft in "HΦ".
    iApply "HΦ".
    {
      done.
    }
  }
Qed.

End pb_setstate_proof.
