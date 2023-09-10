From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof.simplepb Require Export pb_protocol primary_protocol.
From Perennial.program_proof.simplepb Require Import pb_marshal_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_makeclerk_proof.
From Perennial.program_proof.reconnectclient Require Import proof.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Section pb_becomeprimary_proof.
Context `{!heapGS Σ}.
Context {params:pbParams.t}.
Import pbParams.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).

Context `{!waitgroupG Σ}.
Context `{!pbG Σ}.

Lemma wp_Clerk__BecomePrimary γ γsrv ck args_ptr args σ backupγ:
  {{{
        "#Hck" ∷ is_Clerk ck γ γsrv ∗
        (* FIXME: is this epoch_lb needed? *)
        "#Hepoch_lb" ∷ is_epoch_lb γsrv.(r_pb) args.(BecomePrimaryArgs.epoch) ∗
        "#Hconf" ∷ is_epoch_config γ.(s_pb) args.(BecomePrimaryArgs.epoch) (r_pb <$> γsrv :: backupγ) ∗
        "#Hhosts" ∷ ([∗ list] host ; γsrv' ∈ args.(BecomePrimaryArgs.replicas) ; γsrv :: backupγ,
                       is_pb_rpcs host γ γsrv' ∗
                       is_epoch_lb γsrv'.(r_pb) args.(BecomePrimaryArgs.epoch)) ∗
        "#Hprim_escrow" ∷ become_primary_escrow γ.(s_prim) γsrv.(r_prim) args.(BecomePrimaryArgs.epoch) σ
                          (own_primary_ghost γ.(s_pb) args.(BecomePrimaryArgs.epoch) σ) ∗
        "#Hprim_facts" ∷ is_proposal_facts_prim γ.(s_prim) args.(BecomePrimaryArgs.epoch) σ ∗
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
  iDestruct (own_slice_to_small with "Henc_args_sl") as "Henc_args_sl".
  wp_apply (wp_frame_wand with "HΦ").
  rewrite is_pb_rpcs_unfold.
  iNamed "Hsrv".
  wp_apply (wp_ReconnectingClient__Call2 with "Hcl_rpc [] Henc_args_sl Hrep").
  {
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
    iFrame "#".
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

Lemma become_primary_eph_step γ γsrv st σ backupγ replicaHosts:
  st.(server.canBecomePrimary) = true →
  £ 1 -∗
  is_proposal_facts_prim γ.(s_prim) st.(server.epoch) σ -∗
  is_epoch_config γ.(s_pb) st.(server.epoch) (r_pb <$> γsrv :: backupγ) -∗
  ([∗ list] host ; γsrv' ∈ replicaHosts ; γsrv :: backupγ,
                  is_pb_rpcs host γ γsrv' ∗
                  is_epoch_lb γsrv'.(r_pb) st.(server.epoch)) -∗
  become_primary_escrow γ.(s_prim) γsrv.(r_prim) st.(server.epoch) σ
                    (own_primary_ghost γ.(s_pb) st.(server.epoch) σ) -∗
  own_Server_ghost_eph_f st γ γsrv ={↑pbN}=∗
  own_Server_ghost_eph_f (st <| server.isPrimary := true|> <|server.canBecomePrimary := false |>
                         ) γ γsrv.
Proof.
  intros HcanBecome.
  iIntros "Hlc #Hprim_facts_in #Hconf #Hhosts #Hescrow_inv".
  rewrite /own_Server_ghost_eph_f /tc_opaque.
  iNamed 1.
  rewrite /own_Primary_ghost_f /tc_opaque.
  iNamed "Hprimary".
  rewrite HcanBecome.
  iMod (ghost_become_primary with "Hlc Hescrow_inv Hprim_facts Htok") as "HH".
  simpl.
  iClear "Hprim".
  iDestruct "HH" as "(%Hprefix1 & Hprim)".
  iDestruct (ghost_propose_lb_valid with "Hprim Hs_prop_lb") as "%Hprefix2".
  assert (σ = st.(server.ops_full_eph)).
  { apply list_prefix_eq; first done. by apply prefix_length. }
  subst.
  iExists _.
  by iFrame "∗#%".
Qed.

Lemma wp_Server__BecomePrimary γ γsrv s args_ptr args σ backupγ Φ Ψ :
  is_Server s γ γsrv -∗
  BecomePrimaryArgs.own args_ptr args -∗
  (∀ (err:u64), Ψ err -∗ Φ #err) -∗
  BecomePrimary_core_spec γ γsrv args σ backupγ is_pb_rpcs Ψ -∗
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
  iNamed "Hvol".
  iNamed "Hargs".
  wp_loadField.

  iDestruct "HΨ" as "(#Hepoch_lb & #Hconf & #Hhosts & #Hprim_facts & #Hprimary_escrow & HΨ)".

  iAssert (_) with "HisSm" as "HisSm2".
  iNamed "HisSm2".
  wp_loadField.
  wp_apply (wp_or with "[HcanBecomePrimary]").
  { iNamedAccu. }
  { wp_pures. by rewrite -bool_decide_not. }
  { iIntros (_). iNamed 1. wp_loadField. wp_pures. iFrame.
    iPureIntro.
    repeat f_equal.
    instantiate (2:=(st.(server.canBecomePrimary) = false)).
    Unshelve. 2: apply _.
    by destruct (st.(server.canBecomePrimary)).
  }
  iNamed 1.
  wp_if_destruct.
  { (* stale epoch or unable to become primary *)
    wp_loadField.
    unfold BecomePrimary_core_spec.
    wp_apply (release_spec with "[-HΦ HΨ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iFrame "HghostEph".
      repeat (iExists _).
      iFrame "∗#%".
    }
    wp_pures.
    iApply "HΦ".
    iApply "HΨ".
  }
  { (* successfully become primary *)
    (* use is_epoch_lb and accessP property to get that args.epoch <= epoch *)
    wp_storeField.
    wp_pures.

    (* Double for loop to make slice of slices of clerks *)
    replace (#32) with (#numClerks); last done.
    wp_loadField.
    wp_apply (wp_condSignal with "[$]").
    wp_storeField.
    wp_apply (wp_NewSlice).
    iIntros (new_clerkss_sl) "Hnew_clerkss_sl".
    iDestruct (own_slice_to_small with "Hnew_clerkss_sl") as "Hnew_clerkss_sl".

    wp_storeField.
    wp_apply (wp_ref_to).
    { eauto. }
    iIntros (j_ptr) "Hj".
    wp_pures.

    iRename "Hargs_replicas_sl" into "Hreplicas_sl_ro".
      iMod (readonly_load with "Hreplicas_sl_ro") as (?) "Hreplicas_sl".
    iAssert (
          ∃ (j:u64) clerkssComplete clerkssLeft,
            "Hj" ∷ j_ptr ↦[uint64T] #j ∗
            "%HcompleteLens" ∷ ⌜length clerkssComplete = int.nat j⌝ ∗
            "%Hlens" ∷ ⌜length (clerkssComplete ++ clerkssLeft) = numClerks⌝ ∗
            "Hclerkss_sl" ∷ own_slice_small new_clerkss_sl (slice.T ptrT) 1 (clerkssComplete ++ clerkssLeft) ∗
            "#Hclerkss_is" ∷ ([∗ list] clerks_sl ∈ clerkssComplete,
                                  (∃ clerks,
                                  "#Hclerks_sl" ∷ readonly (own_slice_small clerks_sl ptrT 1 clerks) ∗
                                  "Hclerks" ∷ ⌜length clerks = length backupγ⌝ ∗
                                  "#Hclerks_rpc" ∷ ([∗ list] ck ; γsrv' ∈ clerks ; backupγ, is_Clerk ck γ γsrv' ∗ is_epoch_lb γsrv'.(r_pb) args.(BecomePrimaryArgs.epoch))
                                  )
                                )
            )%I with "[Hnew_clerkss_sl Hj]" as "HH".
    {
      iExists _, [], _.
      simpl.
      iFrame "∗#%".
      iSplitL; first done.
      done.
    }
    wp_forBreak_cond.
    (* Now in the outer j-loop, but not in the i-loop yet *)
    iNamed "HH".
    wp_pures.
    wp_load.
    wp_if_destruct.
    { (* continue with the j-loop *)
      wp_pures.

      wp_loadField.
      wp_apply (wp_slice_len).
      wp_apply (wp_NewSlice).
      iIntros (new_clerks_sl) "Hnew_clerks_sl".
      iDestruct (own_slice_to_small with "Hnew_clerks_sl") as "Hnew_clerks_sl".
      wp_pures.
      wp_apply (wp_ref_to).
      { eauto. }
      iIntros (i_ptr) "Hi".
      wp_pures.

      iDestruct (own_slice_small_sz with "Hnew_clerks_sl") as %Hnew_clerks_sz.
      iDestruct (own_slice_small_sz with "Hreplicas_sl") as %Hreplicas_sz.
      iDestruct (big_sepL2_length with "Hhosts") as %Hreplicas_backup_len.

      iAssert (
            ∃ (i:u64) clerksComplete clerksLeft,
              "Hi" ∷ i_ptr ↦[uint64T] #i ∗
              "%HcompleteLen" ∷ ⌜length clerksComplete = int.nat i⌝ ∗
              "%Hlen" ∷ ⌜length (clerksComplete ++ clerksLeft) = length backupγ⌝ ∗
              "Hclerks_sl" ∷ own_slice_small new_clerks_sl ptrT 1 (clerksComplete ++ clerksLeft) ∗
              "#Hclerks_is" ∷ ([∗ list] ck ; γsrv ∈ clerksComplete ; (take (length clerksComplete) backupγ),
                                  pb_definitions.is_Clerk ck γ γsrv ∗
                                  is_epoch_lb γsrv.(r_pb) args.(BecomePrimaryArgs.epoch)
                                  )
              )%I with "[Hnew_clerks_sl Hi]" as "HH".
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
      wp_apply (wp_slice_len).
      (* FIXME: this is quite complicated *)
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
      (* FIXME: the list/for loop reasoning above here should a helper lemma *)

      iRight.
      iSplitR; first done.
      iMod (readonly_alloc_1 with "Hclerks_sl") as "#Hclerks_sl".
      iModIntro.

      wp_pures.
      wp_load.
      wp_loadField.

      assert (numClerks = int.nat numClerks) as HnumClerksSafe.
      { unfold numClerks. word. }

      wp_apply (wp_SliceSet with "[$Hclerkss_sl]").
      {
        iPureIntro.
        apply lookup_lt_is_Some_2.
        rewrite Hlens.
        word.
      }
      iIntros "Hclerkss_sl".
      wp_pures.
      wp_load.
      wp_store.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iFrame "∗#%".

      destruct clerkssLeft.
      { exfalso. rewrite app_nil_r in Hlens. word. }
      rename t0 into x.
      replace (<[int.nat j:=new_clerks_sl]> (clerkssComplete ++ x :: clerkssLeft))
        with
        (((clerkssComplete ++ [new_clerks_sl]) ++ (clerkssLeft))); last first.
      {
        replace (int.nat j) with (length clerkssComplete + 0) by word.
        rewrite insert_app_r.
        rewrite -app_assoc.
        done.
      }

      iExists _, _, _; iFrame "Hj".
      iFrame "∗".
      iSplitR.
      {
        iPureIntro.
        rewrite app_length.
        simpl.
        word.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite app_length.
        rewrite app_length.
        simpl.
        rewrite app_length in Hlens.
        rewrite cons_length in Hlens.
        word.
      }
      iDestruct (big_sepL_app with "[Hclerkss_is]") as "$".
      {
        iFrame "Hclerkss_is".
        iApply big_sepL_singleton.
        iExists (clerksComplete ++ []).
        iFrame "#".
        iSplitL.
        { done. }
        rewrite app_nil_r.
        rewrite take_ge; last first.
        {
          rewrite app_nil_r in Hlen.
          word.
        }
        iFrame "#".
      }
    }
    (* break from j-loop *)

    replace (clerkssLeft) with ([]:list (Slice.t)) in *; last first.
    {
      rewrite app_length in Hlens.
      symmetry.
      apply nil_length_inv.
      rewrite HcompleteLens in Hlens.
      enough (int.nat j ≥ numClerks) by word.
      assert (numClerks = int.nat numClerks) as HnumClerksSafe.
      { unfold numClerks. word. }
      word.
    }
    iRight.
    rewrite app_nil_r.
    iMod (readonly_alloc_1 with "Hclerkss_sl") as "Hclerkss_sl".
    iModIntro.
    iSplitR; first done.

    wp_pure1_credit "Hlc".

    apply Decidable.not_or in Heqb.
    destruct Heqb as [HepochEq Hcan].
    apply dec_stable in HepochEq.
    injection HepochEq as HepochEq.
    rewrite HepochEq.
    iApply fupd_wp.
    iMod (fupd_mask_subseteq (↑pbN)) as "Hmask".
    { set_solver. }
    iMod (become_primary_eph_step with "Hlc Hprim_facts Hconf Hhosts Hprimary_escrow HghostEph") as "HghostEph".
    { by destruct st.(server.canBecomePrimary). }
    iMod "Hmask".
    iModIntro.

    wp_loadField.
    wp_apply (release_spec with "[-HΦ HΨ Hargs_epoch]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      repeat (iExists _).
      iSplitR "HghostEph"; last iFrame.
      repeat (iExists _).
      iFrame "∗#%".
      simpl.
      iRight.
      repeat iExists _.
      iFrame "∗#%".
      iPureIntro. rewrite -Hlens. by rewrite app_nil_r.
    }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iApply "HΨ".
  }
Qed.

End pb_becomeprimary_proof.
