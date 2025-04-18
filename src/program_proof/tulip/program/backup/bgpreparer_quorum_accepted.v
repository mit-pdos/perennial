From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_cquorum.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__quorumAccepted (gpp : loc) phase rk ts gid γ :
    (1 < rk)%nat -> 
    {{{ own_backup_gpreparer_srespm gpp phase rk ts gid γ ∗
        own_backup_gpreparer_nrps gpp
    }}}
      BackupGroupPreparer__quorumAccepted #gpp
    {{{ (ap : bool), RET #ap;
        own_backup_gpreparer_srespm gpp phase rk ts gid γ ∗
        own_backup_gpreparer_nrps gpp ∗
        if ap
        then match phase with
             | BGPPPreparing => quorum_prepared γ gid ts
             | BGPPUnpreparing => quorum_unprepared γ gid ts
             | _ => True
             end
        else True
    }}}.
  Proof.
    iIntros (Hrk Φ) "[Hsrespm Hnrps] HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) quorumAccepted() bool {                 @*)
    (*@     // Count how many replicas have prepared or unprepared, depending on @*)
    (*@     // @gpp.phase.                                                      @*)
    (*@     n := uint64(len(gpp.srespm))                                        @*)
    (*@     return gpp.cquorum(n)                                               @*)
    (*@ }                                                                       @*)
    iNamed "Hsrespm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hsrespm").
    iIntros "[%Hn Hsrespm]".
    wp_apply (wp_BackupGroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    iApply "HΦ".
    iFrame "∗ # %".
    case_bool_decide; last done.
    destruct phase; try done.
    { iExists rk.
      rewrite /quorum_pdec_at_rank.
      case_decide; first word.
      rewrite /= /quorum_fast_pdec.
      iExists (dom srespm).
      iFrame "Hpreps".
      iPureIntro.
      split; first apply Hsincl.
      rewrite /cquorum_size size_dom. word.
    }
    { iExists rk.
      rewrite /quorum_pdec_at_rank.
      case_decide; first word.
      rewrite /= /quorum_fast_pdec.
      iExists (dom srespm).
      iFrame "Hpreps".
      iPureIntro.
      split; first apply Hsincl.
      rewrite /cquorum_size size_dom. word.
    }
  Qed.

End program.
