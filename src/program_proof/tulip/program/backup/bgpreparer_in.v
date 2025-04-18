From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__in (gpp : loc) (phase phasecur : bgppphase) rk ts cid gid γ :
    {{{ own_backup_gpreparer_with_phase gpp phasecur rk ts cid gid γ }}}
      BackupGroupPreparer__in #gpp #(bgppphase_to_u64 phase)
    {{{ RET #(bool_decide (phasecur = phase)); 
        own_backup_gpreparer_with_phase gpp phasecur rk ts cid gid γ
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) in(phase uint64) bool {                 @*)
    (*@     return gpp.phase == phase                                           @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hphase".
    wp_loadField. wp_pures.
    rewrite -Hphase.
    case_bool_decide as Hcase.
    { rewrite Hcase bool_decide_eq_true_2; last done.
      iApply "HΦ".
      by iFrame "∗ # %".
    }
    { rewrite bool_decide_eq_false_2; last first.
      { by destruct phasecur, phase. }
      iApply "HΦ".
      by iFrame "∗ # %".
    }
  Qed.

End program.
