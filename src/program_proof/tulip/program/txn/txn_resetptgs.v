From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__resetptgs (txn : loc) ptgs :
    {{{ own_txn_ptgs txn ptgs }}}
      Txn__resetptgs #txn
    {{{ RET #(); own_txn_ptgs txn [] }}}.
  Proof.
    iIntros (Φ) "Hptgs HΦ".
    wp_rec.

    (*@ func (txn *Txn) resetptgs() {                                           @*)
    (*@     txn.ptgs = txn.ptgs[:0]                                             @*)
    (*@ }                                                                       @*)
    iNamed "Hptgs".
    wp_loadField.
    wp_apply wp_SliceTake; first word.
    wp_storeField.
    iApply "HΦ".
    iDestruct (own_slice_take_cap _ _ _ (W64 0) with "Hptgs") as "Hptgs"; first word.
    iFrame.
    iPureIntro.
    by apply NoDup_nil.
  Qed.

End program.
