From Perennial.program_proof.tulip Require Import prelude.

Section validate.
  Context `{!tulip_ghostG Σ}.

  Lemma replica_inv_validate γ gid rid cpm psptsm ts pwrs :
    (* cm !! ts = None -> *)
    ts ≠ O ->
    dom pwrs ⊆ keys_all ->
    cpm !! ts = None ->
    dom psptsm = dom pwrs ->
    map_Forall (λ _ spts, (spts ≤ ts)%nat) psptsm ->
    (* own_replica_commit_map_half γ rid cm -∗ *)
    is_txn_pwrs γ gid ts pwrs -∗
    own_replica_currently_prepared_map_half γ rid cpm -∗
    ([∗ map] k ↦ spts ∈ psptsm, own_replica_spts_half γ rid k spts) -∗
    ([∗ set] k ∈ dom pwrs, own_replica_pts_half γ rid k O) -∗
    replica_inv γ gid rid ==∗
    (* own_replica_commit_map_half γ rid cm ∗ *)
    own_replica_currently_prepared_map_half γ rid (<[ts := pwrs]> cpm) ∗
    ([∗ set] k ∈ dom pwrs, own_replica_spts_half γ rid k (S ts)) ∗
    ([∗ set] k ∈ dom pwrs, own_replica_pts_half γ rid k ts) ∗
    replica_inv γ gid rid ∗
    is_replica_validated_ts γ gid rid ts.
  Proof.
    iIntros (Hnz Hdompwrs Hnp Hdompsptsm Hgespts) "#Hpwrs Hcpmprog Hpsptsmprog Hpptsmprog Hrp".
    do 2 iNamed "Hrp".
    (* Obtain facts about domain of the timestamp maps. *)
    pose proof (map_Forall2_dom_L _ _ _ Hlenkvd) as Hdomsptsm.
    symmetry in Hdomsptsm. rewrite Hdomkvdm in Hdomsptsm.
    pose proof (map_Forall2_dom_L _ _ _ Hsptsmlk) as Hdomptsm.
    symmetry in Hdomptsm. rewrite Hdomsptsm in Hdomptsm.
    (* Take the relevant smallest preparable/prepare timestamps. *)
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hsptsm") as
      (psptsm' [Hdompsptsm' Hsptsmincl]) "[Hpsptsm Hsptsm]".
    { clear -Hdomsptsm Hdompwrs. set_solver. }
    iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hptsm") as
      (pptsm [Hdompptsm Hptsmincl]) "[Hpptsm Hptsm]".
    { clear -Hdomptsm Hdompwrs. set_solver. }
    (* Agreements. *)
    iDestruct (replica_currently_prepared_map_agree with "Hcpmprog Hcpm") as %->.
    iDestruct (replica_spts_big_agree with "Hpsptsmprog Hpsptsm") as %->.
    { by rewrite Hdompsptsm Hdompsptsm'. }
    iDestruct (big_sepM_gset_to_gmap with "Hpptsmprog") as "Hpptsmprog".
    iDestruct (replica_pts_big_agree with "Hpptsmprog Hpptsm") as %->.
    { by rewrite dom_gset_to_gmap. }
    (* Insert [(ts, pwrs)] into the currently-prepared txn map. *)
    set cpm' := insert _ _ cpm.
    iMod (replica_currently_prepared_map_update cpm' with "Hcpmprog Hcpm")
      as "[Hcpmprog Hcpm]".
    (* Set the smallest preparable timestamp to [S ts]. *)
    set sptsm' := gset_to_gmap (S ts) (dom pwrs).
    iMod (replica_spts_big_update sptsm' with "Hpsptsmprog Hpsptsm")
      as "[Hpsptsmprog Hpsptsm]".
    { by rewrite dom_gset_to_gmap Hdompsptsm. }
    (* Set the prepare timestamp to [ts]. *)
    set ptsm' := gset_to_gmap ts (dom pwrs).
    iMod (replica_pts_big_update ptsm' with "Hpptsmprog Hpptsm") as "[Hpptsmprog Hpptsm]".
    { by rewrite 2!dom_gset_to_gmap. }
    rewrite 2!big_sepM_gset_to_gmap.
    (* Insert [ts] into the set of validated timestamps [vtss]. *)
    iMod (replica_validated_ts_insert ts with "Hvtss") as "Hvtss".
    iDestruct (replica_validated_ts_witness ts with "Hvtss") as "#Htsvd".
    { set_solver. }
    iFrame "Hcpm Hpsptsmprog Hpptsmprog Htsvd".
    (* Put the relevant smallest preparable/prepare timestamps back. *)
    iDestruct (big_sepM_gset_to_gmap with "Hpsptsm") as "Hpsptsm".
    iCombine "Hpsptsm Hsptsm" as "Hsptsm".
    rewrite -big_sepM_union; last first.
    { rewrite map_disjoint_dom dom_gset_to_gmap.
      clear -Hdomsptsm Hdompsptsm. set_solver.
    }
    rewrite map_union_difference_union_L; last first.
    { by rewrite dom_gset_to_gmap Hdompsptsm. }
    iDestruct (big_sepM_gset_to_gmap with "Hpptsm") as "Hpptsm".
    iCombine "Hpptsm Hptsm" as "Hptsm".
    rewrite -big_sepM_union; last first.
    { rewrite map_disjoint_dom dom_gset_to_gmap.
      clear -Hdomptsm Hdompptsm. set_solver.
    }
    rewrite map_union_difference_union_L; last first.
    { by rewrite dom_gset_to_gmap Hdompptsm. }
    (* Extend the validation list for each [k ∈ dom pwrs]. *)
    set extendf := λ (ov : option dbval) (ol : option (list bool)),
                     match ov, ol with
                     | Some _, Some l => Some (extend ts false l ++ [true])
                     | None, Some l => Some l
                     | _, _ => None
                     end.
    set kvdm' := merge extendf pwrs kvdm.
    unshelve epose proof (gmap_nonexpanding_merge_dom pwrs kvdm extendf _)
      as Hdomkvdm'.
    { intros ov ol. by destruct ov, ol. }
    iMod (replica_key_validation_big_update kvdm' with "Hkvdm") as "Hkvdm".
    { rewrite map_Forall2_forall.
      split; last first.
      { symmetry. apply Hdomkvdm'. }
      intros k l l' Hl Hl'.
      destruct (pwrs !! k) as [v |] eqn:Hpwrsk;
        rewrite lookup_merge Hl Hpwrsk /= in Hl'; inv Hl'; last done.
      apply prefix_app_r, extend_prefix.
    }
    (* Obtain witnesses that key [k ∈ dom pwrs] has been validated. *)
    iAssert (validated_pwrs_of_txn γ gid rid ts)%I as "#Hvkeys".
    { iFrame "Hpwrs".
      iDestruct (big_sepM_dom_subseteq_difference _ _ (dom pwrs) with "Hkvdm")
        as (m [Hdomm Hincl]) "[Hkvdm _]".
      { rewrite Hdomkvdm' Hdomkvdm. apply Hdompwrs. }
      iApply (big_sepM_sepS_impl with "Hkvdm"); first apply Hdomm.
      iIntros (k l Hl) "!> Hkvd".
      iDestruct (replica_key_validation_witness with "Hkvd") as "#Hlb".
      iFrame "Hlb".
      iPureIntro.
      pose proof (lookup_weaken _ _ _ _ Hl Hincl) as Hl'.
      apply elem_of_dom_2 in Hl.
      assert (is_Some (pwrs !! k)) as [v Hv].
      { by rewrite -elem_of_dom -Hdomm. }
      assert (is_Some (kvdm !! k)) as [vl Hvl].
      { rewrite -elem_of_dom Hdomkvdm. clear -Hl Hdomm Hdompwrs. set_solver. }
      rewrite lookup_merge Hv Hvl /= in Hl'.
      inv Hl'.
      assert (is_Some (psptsm !! k)) as [spts Hspts].
      { by rewrite -elem_of_dom Hdompsptsm -Hdomm. }
      specialize (Hgespts _ _ Hspts). simpl in Hgespts.
      pose proof (lookup_weaken _ _ _ _ Hspts Hsptsmincl) as Hspts'.
      pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hvl Hspts' Hlenkvd) as Hlenvl.
      simpl in Hlenvl.
      rewrite lookup_snoc_Some.
      right.
      split; last done.
      rewrite extend_length.
      clear -Hlenvl Hgespts. lia.
    }
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { by iApply big_sepM_insert_2. }
    iSplit.
    { by iApply big_sepS_insert_2. }
    iSplit.
    { iIntros (k t).
      admit.
    }
    iPureIntro.
    split.
    { rewrite dom_insert_L. clear -Hvtss. set_solver. }
    split.
    { by rewrite Hdomkvdm'. }
    split.
    { admit. }
    split.
    { admit. }
    split.
    { intros t w k Hw Hk.
      destruct (decide (t = ts)) as [-> | Hne]; last first.
      { rewrite lookup_insert_ne in Hw; last done.
        specialize (Hpil _ _ _ Hw Hk).
        destruct (decide (k ∈ dom pwrs)) as [Hin | Hnotin].
        { exfalso.
          assert (Hz : ptsm !! k = Some O).
          { unshelve eapply (lookup_weaken _ _ _ _ _ Hptsmincl).
            by rewrite lookup_gset_to_gmap_Some.
          }
          clear -Hz Hpil Hw Hcpmnz.
          inv Hz.
        }
        rewrite lookup_union_r; last first.
        { by rewrite lookup_gset_to_gmap_None. }
        apply Hpil.
      }
      rewrite lookup_insert in Hw.
      symmetry in Hw. inv Hw.
      apply lookup_union_Some_l.
      by rewrite lookup_gset_to_gmap_Some.
    }
    { by rewrite lookup_insert_ne. }
  Admitted.

End validate.
