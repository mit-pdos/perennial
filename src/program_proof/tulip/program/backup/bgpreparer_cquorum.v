From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__cquorum (gpp : loc) (n : u64) :
    {{{ own_backup_gpreparer_nrps gpp }}}
      BackupGroupPreparer__cquorum #gpp #n
    {{{ RET #(bool_decide (size rids_all / 2 < uint.Z n)); 
        own_backup_gpreparer_nrps gpp
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) cquorum(n uint64) bool {                @*)
    (*@     return quorum.ClassicQuorum(gpp.nrps) <= n                          @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_apply wp_ClassicQuorum.
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2; first word.
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

End program.
