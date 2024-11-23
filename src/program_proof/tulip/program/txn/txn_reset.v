From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import
  txn_repr txn_resetwrs txn_resetptgs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__reset (txn : loc) wrs q ptgs :
    {{{ own_txn_wrs txn q wrs ∗ own_txn_ptgs txn ptgs }}}
      Txn__reset #txn
    {{{ RET #(); own_txn_wrs txn (DfracOwn 1) ∅ ∗ own_txn_ptgs txn [] }}}.
  Proof.
    iIntros (Φ) "[Hwrs Hptgs] HΦ".
    wp_rec.

    (*@ func (txn *Txn) reset() {                                               @*)
    (*@     txn.resetwrs()                                                      @*)
    (*@     txn.resetptgs()                                                     @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__resetwrs with "Hwrs").
    iIntros "Hwrs".
    wp_apply (wp_Txn__resetptgs with "Hptgs").
    iIntros "Hptgs".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
