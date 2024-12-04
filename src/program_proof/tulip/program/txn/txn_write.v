From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import res txn_repr txn_setwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__Write txn tid key value rds γ τ :
    valid_key key ->
    {{{ own_txn txn tid rds γ τ ∗ (∃ vprev, txnmap_ptsto τ key vprev) }}}
      Txn__Write #txn #(LitString key) #(LitString value)
    {{{ RET #(); own_txn txn tid rds γ τ ∗ txnmap_ptsto τ key (Some value) }}}.
  Proof.
    iIntros (Hvk Φ) "[Htxn [%v Hpt]] HΦ".
    wp_rec.

    (*@ func (txn *Txn) Write(key string, value string) {                       @*)
    (*@     v := tulip.Value{                                                   @*)
    (*@         Present : true,                                                 @*)
    (*@         Content : value,                                                @*)
    (*@     }                                                                   @*)
    (*@     txn.setwrs(key, v)                                                  @*)
    (*@ }                                                                       @*)
    iNamed "Htxn".
    wp_pures.
    wp_apply (wp_Txn__setwrs _ _ (Some value) with "Hwrs").
    { apply Hvk. }
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hpt") as %Hlookup.
    apply elem_of_dom_2 in Hlookup.
    iMod (txnmap_update (Some value) with "Htxnmap Hpt") as "[Htxnmap Hpt]".
    rewrite insert_union_l.
    iFrame "∗ # %".
    iPureIntro.
    rewrite /valid_wrs dom_insert_L.
    set_solver.
  Qed.

End program.
