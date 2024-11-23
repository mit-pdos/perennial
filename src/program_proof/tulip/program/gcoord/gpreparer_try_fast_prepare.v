From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import count_bool_map.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_fquorum.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__tryFastPrepare (gpp : loc) ts gid γ :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__tryFastPrepare #gpp
    {{{ (prepared : bool), RET #prepared; own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryFastPrepare() bool {                       @*)
    (*@     // Count how many replicas have fast prepared.                      @*)
    (*@     n := util.CountBoolMap(gpp.frespm, true)                            @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgpp". iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (n) "[Hfrespm %Hn]".
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { by iFrame "∗ # %". }

    (*@     // Move to the PREPARED phase if obtaining a fast quorum of fast prepares. @*)
    (*@     if gpp.fquorum(n) {                                                 @*)
    (*@         gpp.phase = GPP_PREPARED                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__fquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hfq; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iExists GPPPrepared.
      iFrame "∗ #".
      iSplit; first done.
      iSplitL "Hsrespm".
      { iNamed "Hsrespm". by iFrame "∗ %". }
      iSplit; first done.
      set frespmq := filter _ _ in Hn.
      iSplit.
      { (* Prove [quorum_prepared]. *)
        iExists O.
        rewrite /quorum_pdec_at_rank.
        case_decide; last done.
        iExists (dom frespmq).
        iSplit; last first.
        { iPureIntro.
          split.
          { etrans; last apply Hfincl. apply dom_filter_subseteq. }
          { destruct Hfq as [Hfq Hnz].
            split; last done.
            rewrite size_dom.
            clear -Hfq Hn. word.
          }
        }
        rewrite /fast_prepare_responses.
        iDestruct (big_sepM_subseteq _ _ frespmq with "Hfast") as "Hfastq".
        { apply map_filter_subseteq. }
        rewrite big_sepS_big_sepM.
        iApply (big_sepM_mono with "Hfastq").
        iIntros (rid b Hb) "[Hpdec _]".
        apply map_lookup_filter_Some in Hb as [_ Hb]. simpl in Hb.
        by subst b.
      }
      { (* Prove [quorum_validated]. *)
        iExists (dom frespmq).
        iSplit; last first.
        { iPureIntro.
          split.
          { etrans; last apply Hfincl. apply dom_filter_subseteq. }
          { destruct Hfq as [Hfq Hnz].
            rewrite /cquorum_size size_dom.
            clear -Hfq Hn Hnz. word.
          }
        }
        rewrite /fast_prepare_responses.
        iDestruct (big_sepM_subseteq _ _ frespmq with "Hfast") as "Hfastq".
        { apply map_filter_subseteq. }
        iDestruct (big_sepM_sep with "Hfastq") as "[_ Hvdq]".
        rewrite big_sepS_big_sepM.
        iApply (big_sepM_mono with "Hvdq").
        iIntros (rid b Hb) "Hvd".
        apply map_lookup_filter_Some in Hb as [_ Hb]. simpl in Hb.
        by subst b.
      }
    }
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
