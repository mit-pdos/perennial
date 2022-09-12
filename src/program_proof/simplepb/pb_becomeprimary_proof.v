From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Perennial.program_proof.simplepb Require Export pb_ghost.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_makeclerk_proof.

(* FIXME: for `list_copy_one_more_element` *)
From Perennial.program_proof.simplepb Require Import config_marshal_proof.

Section pb_becomeprimary_proof.
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

Lemma wp_Clerk__BecomePrimary γ γsrv ck args_ptr args σ backupγ:
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        "#Hepoch_lb" ∷ is_epoch_lb γsrv args.(BecomePrimaryArgs.epoch) ∗
        "#Hconf" ∷ is_epoch_config γ args.(BecomePrimaryArgs.epoch) (γsrv :: backupγ) ∗
        (* FIXME: want this to be "is_pb_host", but that will require recursion *)
        "#Hhosts" ∷ ([∗ list] host ; γsrv' ∈ args.(BecomePrimaryArgs.replicas) ; γsrv :: backupγ,
                       is_pb_host host γ γsrv' ∗
                       is_epoch_lb γsrv' args.(BecomePrimaryArgs.epoch)) ∗
        "#Hprop_lb" ∷ is_proposal_lb γ args.(BecomePrimaryArgs.epoch) σ ∗
        "#Hprop_facts" ∷ is_proposal_facts γ args.(BecomePrimaryArgs.epoch) σ ∗
        "#Hprim_escrow" ∷ become_primary_escrow γ γsrv args.(BecomePrimaryArgs.epoch) σ ∗
        "Hargs" ∷ BecomePrimaryArgs.own args_ptr args
  }}}
    Clerk__BecomePrimary #ck #args_ptr
  {{{
        (err:u64), RET #err; True
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
  wp_apply (BecomePrimaryArgs.wp_Encode with "[$Hargs]").
  iIntros (enc_args enc_args_sl) "(%Henc_args & Henc_args_sl & Hargs)".
  wp_loadField.
  iDestruct (is_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  wp_apply (wp_Client__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
    rewrite is_pb_host_unfold.
    iDestruct "Hsrv" as "[_ [_ [_ [$ _]]]]".
  }
  { (* Successful RPC *)
    iModIntro.
    iNext.
    unfold BecomePrimary_spec.
    iExists _, _, _.
    iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done.
    simpl.
    iFrame "Hhosts".
    iFrame "Hprop_lb Hprop_facts Hprim_escrow".
    (* BecomePrimary was rejected by the server (e.g. stale epoch number) *)
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
    done.
  }
  { (* RPC error *)
    iIntros.
    wp_pures.
    wp_if_destruct.
    {
      iModIntro.
      iIntros "HΦ".
      iApply "HΦ".
      done.
    }
    { exfalso. done. }
  }
Qed.

Lemma wp_Server__BecomePrimary γ γsrv s args_ptr args σ backupγ Φ Ψ :
  is_Server s γ γsrv -∗
  BecomePrimaryArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  BecomePrimary_core_spec γ γsrv args σ backupγ is_pb_host Ψ -∗
  WP pb.Server__BecomePrimary #s #args_ptr {{ Φ }}
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

  iDestruct "HΨ" as "(#Hepoch_lb & #Hconf & #Hhosts & #Hprimary_escrow & #Hprop_lb & #Hprop_facts & HΨ)".

  iAssert (_) with "HisSm" as "HisSm2".
  iNamed "HisSm2".
  wp_apply (wp_Server__isEpochStale with "[$Hepoch_lb $HaccP $Hstate $Hepoch]").
  iIntros "(%Hepoch_ge & Hepoch & Hstate)".
  wp_if_destruct.
  { (* stale epoch *)
    wp_loadField.
    unfold BecomePrimary_core_spec.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "∗ HisSm #%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "HΨ".
  }
  { (* successfully become primary *)
    assert (args.(BecomePrimaryArgs.epoch) = epoch) as Hepoch_eq.
    { word. }
    wp_storeField.
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_apply (wp_NewSlice).
    iIntros (new_clerks_sl) "Hnew_clerks_sl".
    iDestruct (is_slice_to_small with "Hnew_clerks_sl") as "Hnew_clerks_sl".
    wp_storeField.
    wp_apply (wp_ref_to).
    { eauto. }
    iIntros (i_ptr) "Hi".
    wp_pures.

    iDestruct (is_slice_small_sz with "Hnew_clerks_sl") as %Hnew_clerks_sz.
    iDestruct (is_slice_small_sz with "Hargs_replicas_sl") as %Hreplicas_sz.
    iDestruct (big_sepL2_length with "Hhosts") as %Hreplicas_backup_len.

    iAssert (
          ∃ (i:u64) clerksComplete clerksLeft,
            "Hi" ∷ i_ptr ↦[uint64T] #i ∗
            "%HcompleteLen" ∷ ⌜length clerksComplete = int.nat i⌝ ∗
            "%Hlen" ∷ ⌜length (clerksComplete ++ clerksLeft) = length backupγ⌝ ∗
            "Hclerks_sl" ∷ is_slice_small new_clerks_sl ptrT 1 (clerksComplete ++ clerksLeft) ∗
            "Hreplicas_sl" ∷ is_slice_small replicas_sl uint64T 1 args.(BecomePrimaryArgs.replicas) ∗
            "#Hclerks_is" ∷ ([∗ list] ck ; γsrv ∈ clerksComplete ; (take (length clerksComplete) backupγ),
                                pb_definitions.is_Clerk ck γ γsrv ∗
                                is_epoch_lb γsrv args.(BecomePrimaryArgs.epoch)
                                )
            )%I with "[Hnew_clerks_sl Hargs_replicas_sl Hi]" as "HH".
    {
      iExists _, [], _.
      simpl.
      iFrame "∗#".
      iPureIntro.
      split; first word.
      rewrite replicate_length.
      rewrite cons_length /= in Hreplicas_backup_len.
      rewrite Hreplicas_sz in Hreplicas_backup_len.
      word.
    }

    wp_forBreak_cond.
    iNamed "HH".

    wp_pures.
    wp_load.
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_if_destruct.
    { (* continue with loop *)
      assert (int.nat i < length backupγ) as Hi.
      { (* XXX: annoying proof *)
        rewrite cons_length /= Hreplicas_sz in Hreplicas_backup_len.
        rewrite replicate_length in Hnew_clerks_sz.

        rewrite app_length in Hlen.
        rewrite HcompleteLen in Hlen.
        replace (length backupγ) with (length args.(BecomePrimaryArgs.replicas) - 1) by word.
        rewrite Hreplicas_sz.
        assert (int.nat i < int.nat new_clerks_sl.(Slice.sz)) by word.
        rewrite -Hnew_clerks_sz in H.
        replace (int.nat replicas_sl.(Slice.sz) - 1) with (int.nat (word.sub replicas_sl.(Slice.sz) 1%Z)).
        { done. }
        word.
      }
      pose proof Hi as Hlookup.
      apply list_lookup_lt in Hlookup as [γsrv' Hlookup].
      assert (([γsrv] ++ backupγ) !! (int.nat i + 1) = Some γsrv').
      {
        rewrite lookup_app_r.
        {
          simpl. rewrite -Hlookup.
          f_equal. word.
        }
        {
          simpl. word.
        }
      }
      iDestruct (big_sepL2_lookup_2_some with "Hhosts") as "%Hlookup_replicas".
      {
        done.
      }
      destruct Hlookup_replicas as [replica_host Hlookup_replicas].
      wp_pures.
      wp_load.
      wp_loadField.
      wp_apply (wp_SliceGet with "[$Hreplicas_sl]").
      {
        iPureIntro.
        replace (int.nat (word.add i 1%Z)) with (int.nat i + 1) by word.
        done.
      }
      iIntros "Hreplicas_sl".
      wp_apply (wp_MakeClerk with "[]").
      {
        instantiate (1:=γsrv').
        instantiate (1:=γ).
        iDestruct (big_sepL2_lookup_acc with "Hhosts") as "[[$ _] _]".
        { done. }
        { done. }
      }
      iIntros (ck) "#Hck".
      wp_load.
      wp_loadField.
      wp_apply (wp_SliceSet (V:=loc) with "[$Hclerks_sl]").
      {
        iPureIntro.
        apply lookup_lt_is_Some_2.
        word.
      }
      iIntros "Hclerks_sl".
      wp_pures.
      wp_load.
      wp_store.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iFrame "∗".

      destruct clerksLeft.
      { exfalso. rewrite app_nil_r in Hlen. word. }
      replace (<[int.nat i:=ck]> (clerksComplete ++ l :: clerksLeft))
              with
          (((clerksComplete ++ [ck]) ++ (clerksLeft))); last first.
      {
        replace (int.nat i) with (length clerksComplete + 0) by word.
        rewrite insert_app_r.
        rewrite -app_assoc.
        done.
      }

      iExists _, _, _.
      iFrame "∗".
      iSplitL; first iPureIntro.
      {
        rewrite app_length /=.
        word.
      }
      iSplitL; first iPureIntro.
      {
        rewrite app_length.
        rewrite app_length.
        simpl.
        rewrite app_length in Hlen.
        rewrite cons_length in Hlen.
        word.
      }
      replace (take (length (clerksComplete ++ [ck])) backupγ)
              with
              ((take (length clerksComplete) backupγ) ++ [γsrv']); last first.
      {
        rewrite app_length.
        simpl.
        rewrite take_more; last first.
        { word. }
        f_equal.
        apply list_eq.
        intros.
        destruct i0.
        {
          simpl.
          rewrite lookup_take; last first.
          { lia. }
          rewrite lookup_drop.
          rewrite HcompleteLen.
          rewrite -H.
          simpl.
          replace (int.nat i + 1) with (S (int.nat i)) by word.
          rewrite lookup_cons.
          f_equal. word.
        }
        simpl.
        rewrite lookup_nil.
        rewrite lookup_take_ge.
        { done. }
        word.
      }
      iApply (big_sepL2_app with "Hclerks_is").
      simpl.
      iFrame "Hck".
      iDestruct (big_sepL2_lookup_acc with "Hhosts") as "[[_ $] _]".
      { done. }
      { done. }
    }
    (* done with loop *)
    replace (clerksLeft) with ([]:list loc) in *; last first.
    {
      rewrite app_length in Hlen.
      symmetry.
      apply nil_length_inv.
      rewrite HcompleteLen in Hlen.
      enough (int.nat i ≥ length backupγ) by word.
      rewrite cons_length in Hreplicas_backup_len.
      replace (length backupγ) with (length args.(BecomePrimaryArgs.replicas) - 1); last first.
      { (* FIXME: why doesn't word work on is own? *)
        rewrite Hreplicas_backup_len.
        word.
      }
      rewrite Hreplicas_sz.
      rewrite replicate_length in Hnew_clerks_sz.
      assert (int.nat i ≥ int.nat new_clerks_sl.(Slice.sz)) by word.
      rewrite -Hnew_clerks_sz in H.
      replace (int.nat replicas_sl.(Slice.sz) - 1) with (int.nat (word.sub replicas_sl.(Slice.sz) 1%Z)).
      { done. }
      (* FIXME: why doesn't word work here anymore? *)
      enough (int.nat (replicas_sl.(Slice.sz)) > 0).
      { word. }
      rewrite -Hreplicas_sz.
      rewrite Hreplicas_backup_len.
      word.
    }

    iRight.
    iSplitR; first done.
    iMod (readonly_alloc_1 with "Hclerks_sl") as "Hclerks_sl".
    iModIntro.
    wp_pure1_credit "Hlc".
    wp_pures.
    iApply fupd_wp.
    iMod ("HaccP" with "[Hlc] Hstate") as "Hstate".
    {
      iIntros "Hghost".
      iDestruct "Hghost" as (?) "(%Hre & Hghost & Hprim)".
      rewrite Hepoch_eq.
      iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
      { set_solver. }
      iDestruct (ghost_helper1 with "Hs_prop_lb Hghost") as %->.
      { do 2 (rewrite -(fmap_length fst)). rewrite -Hre. done. }
      iMod (ghost_become_primary with "Hlc Hprimary_escrow Hs_prop_lb Hprim") as "HH".
      iDestruct "HH" as "[Hprim #His_tok]".
      instantiate (1:=is_tok γsrv epoch).
      iMod "Hmask".
      iModIntro.
      iSplitL; last iFrame "His_tok".
      iExists _.
      iFrame.
      done.
    }
    iModIntro.
    wp_bind (struct.loadF _ _ _)%I.
    wp_apply (wpc_nval_elim_wp with "Hstate").
    { done. }
    { done. }
    wp_loadField.
    iIntros "[Hstate #His_tok]".
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _, _, _, _, _, _, _.
      iFrame "HisPrimary ∗ HisSm #%".
      iExists _, _.
      rewrite Hepoch_eq.
      iFrame "Hclerks_sl Hconf".
      iSplitL ""; first done.
      rewrite app_nil_r.
      rewrite take_ge; last first.
      {
        rewrite app_nil_r in Hlen.
        word.
      }
      iApply (big_sepL2_impl with "Hclerks_is").
      iModIntro.
      iIntros.
      iFrame "#".
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
  }
Qed.

End pb_becomeprimary_proof.
