From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr txn_resetwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__reset (txn : loc) wrs q :
    {{{ own_txn_wrs txn q wrs }}}
      Txn__reset #txn
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) ∅ }}}.
  Proof.
    iIntros (Φ) "Hwrs HΦ".
    wp_rec.

    (*@ func (txn *Txn) reset() {                                               @*)
    (*@     txn.resetwrs()                                                      @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__resetwrs with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
