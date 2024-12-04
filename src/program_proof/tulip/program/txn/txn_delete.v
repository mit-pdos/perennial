From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import res txn_repr txn_setwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__Delete txn tid key rds γ τ :
    valid_key key ->
    {{{ own_txn txn tid rds γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Delete #txn #(LitString key)
    {{{ RET #(); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key None }}}.
  Proof.
    iIntros (Hvk Φ) "[Htxn [%v Hpt]] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Delete(key string) {                                    @*)
    (*@     v := tulip.Value{                                                   @*)
    (*@         Present : false,                                                @*)
    (*@     }                                                                   @*)
    (*@     txn.setwrs(key, v)                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Htxn".
    wp_pures.
    wp_apply (wp_Txn__setwrs _ _ None with "Hwrs").
    { apply Hvk. }
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hlookup.
    apply elem_of_dom_2 in Hlookup.
    iMod (txnmap_update None with "Htxnmap Hpt") as "[Htxnmap Hpt]".
    rewrite insert_union_l.
    iFrame "∗ # %".
    iPureIntro.
    rewrite /valid_wrs dom_insert_L.
    set_solver.
  Qed.

End program.
