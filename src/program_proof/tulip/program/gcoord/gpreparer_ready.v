From Perennial.program_proof.tulip.invariance Require Import propose.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__ready (gpp : loc) phase :
    {{{ own_gpreparer_phase gpp phase }}}
      GroupPreparer__ready #gpp
    {{{ RET #(bool_decide (gpp_ready phase)); own_gpreparer_phase gpp phase }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) ready() bool {                                @*)
    (*@     return GPP_PREPARED <= gpp.phase                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_pures.
    rewrite /gppphase_to_u64 in Hphase.
    rewrite /gpp_ready.
    case_bool_decide as Hcond.
    { case_bool_decide as Hret.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
    { case_bool_decide as Hret; last first.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
  Qed.

  Theorem wp_GroupPreparer__ready_external (gpp : loc) phase ts gid γ :
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__ready #gpp
    {{{ RET #(bool_decide (gpp_ready phase)); own_gpreparer_with_phase gpp phase ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    iNamed "Hgpp".
    wp_apply (wp_GroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
