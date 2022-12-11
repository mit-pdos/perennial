From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From Perennial.program_proof.reconnectclient Require Import proof.

Section pb_setstate_proof.
Context `{!heapGS Σ}.
Context {pb_record:PBRecord}.

Notation OpType := (pb_OpType pb_record).
Notation has_op_encoding := (pb_has_op_encoding pb_record).
Notation has_snap_encoding := (pb_has_snap_encoding pb_record).
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
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    rewrite is_pb_host_unfold.
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

Lemma wp_Server__SetState γ γsrv s args_ptr args σ Φ Ψ :
  is_Server s γ γsrv -∗
  SetStateArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  SetState_core_spec γ γsrv args σ Ψ -∗
  WP pb.Server__SetState #s #args_ptr {{ Φ }}
  .
Proof.
  iIntros "#His_srv Hargs HΦ HΨ".
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
    iDestruct "HΨ" as "(_ & _ & _ & _ & HΨ)".
    iRight in "HΨ".
    wp_apply (release_spec with "[-HΨ HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      do 9 (iExists _).
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "HΨ".
    done.
  }
  { (* successfully set the state *)
    wp_loadField.
    wp_loadField.
    wp_if_destruct.
    { (* state has been set previously. Use is_prop_lb to get agreement. *)
      wp_loadField.

      iDestruct "HΨ" as "(_ & _ & _ & _ & HΨ)".
      iLeft in "HΨ".
      wp_apply (release_spec with "[-HΨ HΦ]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        do 9 (iExists _).
        iFrame "∗#%".
      }
      wp_pures.
      iApply "HΦ".
      iApply "HΨ".
      iFrame "#". done.
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

    iDestruct "HΨ" as "(%Henc_snap &  %Hlen_nooverflow & #Hprop_lb & #Hprop_facts & HΨ)".
    replace (args.(SetStateArgs.nextIndex)) with (U64 (length σ)) by word.
    replace (length σ) with (length σ.*1); last first.
    { by rewrite fmap_length. }

    wp_apply ("HsetStateSpec" with "[$Hstate]").
    {
      iSplitR; first done.
      iFrame "Hargs_state_sl".
      iIntros "Hghost".
      iDestruct "Hghost" as (?) "(%Heq & Hghost & Hprim)".

      assert (int.nat epoch < int.nat args.(SetStateArgs.epoch)) as Hepoch_fresh.
      {
        assert (int.nat epoch ≠ int.nat args.(SetStateArgs.epoch)).
        {
          assert (int.nat epoch ≠ int.nat args.(SetStateArgs.epoch) ∨
        (int.nat epoch = int.nat args.(SetStateArgs.epoch))) as [|].
          { word. }
          { word. }
          { exfalso. replace (epoch) with (args.(SetStateArgs.epoch)) in * by word.
            done. }
        }
        word.
      }

      iMod (ghost_accept_and_unseal with "Hghost Hprop_lb [$]") as "Hghost".
      {
        done.
      }

      iMod (ghost_primary_accept_new_epoch with "Hprop_facts Hprop_lb Hprim") as "Hprim".
      {
        done.
      }
      iDestruct (ghost_get_epoch_lb with "Hghost") as "#Hepoch_lb".
      iDestruct (ghost_get_accepted_lb with "Hghost") as "#Hacc_lb".
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

    (* signal all opApplied condvars *)
    wp_apply (wp_MapIter with "HopAppliedConds_map HopAppliedConds_conds").
    { iFrame "HopAppliedConds_conds". }
    { (* prove one iteration of the map for loop *)
      iIntros.
      iIntros (?) "!# [_ #Hpre] HΦ".
      wp_pures.
      wp_apply (wp_condSignal with "Hpre").
      iApply "HΦ".
      iFrame "#".
      instantiate (1:=(λ _ _, True)%I).
      done.
    }
    iIntros "(HopAppliedConds_map & _ & _)".

    wp_pures.
    wp_apply (wp_NewMap).
    iIntros (opAppliedConds_loc_new) "Hmapnew".
    wp_storeField.

    wp_loadField.
    wp_apply (release_spec with "[-HΨ HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      do 9 (iExists _).
      iFrame "∗ HisSm #%".
      iSplit.
      {
        iPureIntro.
        rewrite fmap_length.
        word.
      }
      iSplitL; last done.
      by iApply big_sepM_empty.
    }
    wp_pures.
    iLeft in "HΨ".
    iApply "HΦ".
    iApply "HΨ".
    {
      done.
    }
  }
Qed.

End pb_setstate_proof.
