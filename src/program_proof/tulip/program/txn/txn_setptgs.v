From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__setptgs txn q wrs :
    {{{ own_txn_wrs txn q wrs ∗ own_txn_ptgs_empty txn }}}
      Txn__setptgs #txn
    {{{ RET #();
        own_txn_wrs txn q wrs ∗ own_txn_ptgs_fixed txn (ptgroups (dom wrs))
    }}}.
  Proof using heapGS0 tulip_ghostG0 Σ.
    iIntros (Φ) "[Hwrs Hptgs] HΦ".
    wp_rec.

    (*@ func (txn *Txn) setptgs() {                                             @*)
    (*@     var ptgs = make([]uint64, 0, 1)                                     @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hptgs".
    rewrite uint_nat_W64_0 /=.
    wp_apply wp_ref_to; first apply slice_val_ty.
    iIntros (ptgsP) "HptgsP".

    (*@     for gid, pwrs := range(txn.wrs) {                                   @*)
    (*@         if uint64(len(pwrs)) != 0 {                                     @*)
    (*@             ptgs = append(ptgs, gid)                                    @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@     txn.ptgs = ptgs                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hwrs".
    wp_loadField.
    set P := (λ (mx : gmap u64 loc),
      ∃ (s : Slice.t) (ptgs : list u64),
        "HptgsP" ∷ ptgsP ↦[slice.T uint64T] (to_val s) ∗
        "Hptgs"  ∷ own_slice s uint64T (DfracOwn 1) ptgs ∗
        "Hpwrsm" ∷ ([∗ map] p;m ∈ pwrsmP;pwrsm, own_map p q m) ∗
        "%Hnd"   ∷ ⌜NoDup ptgs⌝ ∗
        "%Hincl" ∷ ⌜Forall (λ g, g ∈ dom mx) ptgs⌝ ∗
        (* non-empty ↔ in ptgs *)
        "%Hspec" ∷ ⌜set_Forall (λ g, keys_group g (dom wrs) ≠ ∅ ↔ g ∈ ptgs) (dom mx)⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "HpwrsmP [$HptgsP $Hptgs $Hpwrsm]").
    { iPureIntro. by split; first apply NoDup_nil. }
    { clear Φ.
      iIntros (m gid pwrsP Φ) "!> [HP [%Hnone %Hsome]] HΦ".
      iNamed "HP".
      iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
      { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
        iPureIntro.
        by rewrite -elem_of_dom -Hdom elem_of_dom.
      }
      iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].
      wp_apply (wp_MapLen with "Hpwrs").
      iIntros "[%Hsize Hpwrs]".
      iDestruct ("HpwrsmC" with "Hpwrs") as "Hpwrsm".
      wp_if_destruct.
      { wp_load.
        (* NB: need to provide [own_slice] to properly resolve the right typeclass. *)
        wp_apply (wp_SliceAppend with "Hptgs").
        iIntros (s') "Hptgs".
        wp_store.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        split.
        { apply NoDup_snoc; last apply Hnd.
          intros Hgid.
          rewrite Forall_forall in Hincl.
          specialize (Hincl _ Hgid).
          by apply not_elem_of_dom in Hnone.
        }
        split.
        { rewrite Forall_app Forall_singleton dom_insert_L.
          split; last set_solver.
          apply (Forall_impl _ _ _ Hincl).
          set_solver.
        }
        intros g Hg.
        rewrite dom_insert_L elem_of_union in Hg.
        split.
        { intros Hne.
          destruct Hg as [? | Hg]; first set_solver.
          specialize (Hspec _ Hg). simpl in Hspec.
          set_solver.
        }
        { intros Hsnoc.
          destruct Hg as [Hgid | Hg]; last first.
          { specialize (Hspec _ Hg). simpl in Hspec.
            apply Hspec.
            rewrite -not_elem_of_dom in Hnone.
            set_solver.
          }
          rewrite elem_of_singleton in Hgid.
          subst g.
          unfold dbmap in *. (* XXX: this is because some occurrences of dbmap
                                are unfolded (perhaps because of lemmas like wp_MapLen). *)
          assert (Hnz : (size pwrs ≠ O)) by word.
          clear Heqb.
          specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
          intros Hempty.
          rewrite -wrs_group_keys_group_dom -Hwrsg in Hempty.
          apply dom_empty_inv_L in Hempty.
          by rewrite map_size_non_empty_iff in Hnz.
        }
      }
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite dom_insert_L.
      split; first apply Hnd.
      split.
      { apply (Forall_impl _ _ _ Hincl). set_solver. }
      apply set_Forall_union; last apply Hspec.
      rewrite set_Forall_singleton.
      assert (Hsizez : size pwrs = O).
      { rewrite Heqb in Hsize. done. }
      split.
      { intros Hne.
        specialize (Hwrsg _ _ Hpwrs). simpl in Hwrsg.
        rewrite -wrs_group_keys_group_dom -Hwrsg in Hne.
        apply map_size_empty_inv in Hsizez.
        by rewrite Hsizez in Hne.
      }
      { intros Hinptgs.
        rewrite Forall_forall in Hincl.
        specialize (Hincl _ Hinptgs).
        by rewrite -not_elem_of_dom in Hnone.
      }
    }
    iIntros "[HpwrsmP HP]". 
    iNamed "HP".
    wp_load. wp_storeField.
    iApply "HΦ".
    iDestruct (own_slice_to_small with "Hptgs") as "Hptgs".
    iMod (own_slice_small_persist with "Hptgs") as "#Hptgs'".
    iFrame "∗ # %".
    iPureIntro.
    apply set_eq.
    intros gid.
    rewrite elem_of_ptgroups elem_of_list_to_set.
    split.
    { intros Hgid.
      rewrite Forall_forall in Hincl.
      specialize (Hincl _ Hgid).
      specialize (Hspec _ Hincl). simpl in Hspec.
      by apply Hspec.
    }
    { intros Hne.
      destruct (decide (gid ∈ gids_all)) as [Hin | Hnotin]; last first.
      { rewrite /keys_group in Hne.
        apply set_choose_L in Hne as [k Hk].
        pose proof (elem_of_key_to_group k) as Hin.
        set_solver.
      }
      rewrite Hdomwrs in Hspec.
      specialize (Hspec _ Hin). simpl in Hspec.
      by apply Hspec.
    }
  Qed.

End program.
