From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__latestProposal (gpp : loc) pps rk ts cid gid γ :
    pps ≠ ∅ ->
    {{{ own_backup_gpreparer_pps gpp pps rk ts cid gid γ }}}
      BackupGroupPreparer__latestProposal #gpp
    {{{ (p : ppsl), RET (ppsl_to_val p);
        own_backup_gpreparer_pps gpp pps rk ts cid gid γ ∗
        ⌜p ∈ (map_img pps : gset ppsl)⌝ ∧
        ⌜map_Forall (λ _ x, (uint.nat x.1 ≤ uint.nat p.1)%nat) pps⌝
    }}}.
  Proof.
    (*@ func (gpp *BackupGroupPreparer) latestProposal() tulip.PrepareProposal { @*)
    (*@     var latest tulip.PrepareProposal                                    @*)
    (*@                                                                         @*)
    (*@     for _, pp := range(gpp.pps) {                                       @*)
    (*@         if latest.Rank < pp.Rank {                                      @*)
    (*@             latest = pp                                                 @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return latest                                                       @*)
    (*@ }                                                                       @*)
    iIntros (Hps Φ) "Hown HΦ".
    wp_rec.
    wp_apply (typed_mem.wp_AllocAt); [val_ty|].
    iIntros (l) "(Hl&Htok)".
    iEval (rewrite /own_backup_gpreparer_pps) in "Hown"; iNamed "Hown".
    wp_pures.
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ (m : gmap w64 ppsl),
                                            ∃ p, l ↦[uint64T * (boolT * unitT)%ht] (ppsl_to_val p) ∗
                                                   (⌜ p ∈ (map_img m : gset ppsl) ∨ (m = ∅ ∧ p.1 = (W64 0))⌝) ∗
                                                   ⌜ map_Forall (λ _ x, (uint.nat x.1 ≤ uint.nat p.1)%nat) m⌝)%I
                              pps
               with "Hpps [Hl]").
    { rewrite /zero_val//=. iExists (W64 0, false). iFrame "Hl".
      iPureIntro; split.
      - right; eauto.
      - apply map_Forall_empty. }
    { iIntros (m0 k v).
      iIntros (Φ') "!> H HΦ'".
      iDestruct "H" as "(Hpred&%Hlook)".
      destruct Hlook as (Hlook1&Hlook2).
      iDestruct "Hpred" as (p) "(Hl&%Hm&%Hforall)".
      wp_pures. wp_load. wp_pures. wp_if_destruct.
      - wp_store. iApply "HΦ'".
        iModIntro. iExists _. iFrame. iPureIntro.
        split.
        * left. apply elem_of_map_img_insert.
        * apply map_Forall_insert; first by intuition eauto.
          split; auto.
          eapply map_Forall_impl; eauto. simpl. intros. lia.
      - iApply "HΦ'".
        iModIntro. iExists _. iFrame. iPureIntro.
        split.
        * left. apply elem_of_map_img.
          destruct Hm as [Hin|Hemp]; last first.
          { destruct Hemp as (?&Heq). rewrite Heq in Heqb. word. }
          apply elem_of_map_img in Hin as (i&Hin).
          exists i. rewrite lookup_insert_ne //; congruence.
        * apply map_Forall_insert; first by intuition eauto.
          split; auto.
          word.
    }
    iIntros "(Hown&Hp)". iDestruct "Hp" as (p) "(Hl&%Hin&%Hforall)".
    wp_pures. wp_load.
    iModIntro. iApply"HΦ".
    iSplitR "".
    { iExists _, _. iFrame "∗ # %". }
    iPureIntro; split; auto.
    intuition.
  Qed.

End program.
