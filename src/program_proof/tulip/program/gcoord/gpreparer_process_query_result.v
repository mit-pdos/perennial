From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_try_resign.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__processQueryResult
    (gpp : loc) (res : rpres) ts gid γ :
    query_outcome γ ts res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processQueryResult #gpp #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros "#Hquery".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processQueryResult(rid uint64, res uint64) {  @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     gpp.tryResign(res)                                                  @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
