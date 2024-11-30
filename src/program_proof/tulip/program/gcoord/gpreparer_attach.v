From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__attach (gpp : loc) ts gid γ :
    {{{ own_gpreparer_uninit gpp ∗ own_txn_client_token γ ts gid }}}
      GroupPreparer__attach #gpp
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "[Hgpp Hcli] HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) reset() {                                     @*)
    (*@     gpp.phase = GPP_VALIDATING                                          @*)
    (*@     gpp.frespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.vdm = make(map[uint64]bool)                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (frespmP') "Hfrespm".
    wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (vdmP') "Hvdm".
    wp_storeField.
    iApply "HΦ".
    iFrame "HphaseP HfrespmP HvdmP HsrespmP ∗ %".
    iExists GPPValidating. simpl.
    iModIntro.
    iSplit; first done.
    iSplit.
    { iSplit; last done. by iApply big_sepM_empty. }
    iSplit.
    { iSplit; last done. by rewrite /validation_responses dom_empty_L big_sepS_empty. }
    iSplit.
    { iExists ∅. done. }
    by iFrame.
  Qed.

End program.
