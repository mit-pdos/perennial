From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gpreparer_repr greader_repr gpreparer_attach greader_reset.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Attach (gcoord : loc) (tsW : u64) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ own_txn_client_token γ ts gid }}}
      GroupCoordinator__Attach #gcoord #tsW
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> Hcli HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Attach(ts uint64) {                     @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     gcoord.ts = ts                                                      @*)
    (*@     gcoord.grd.reset()                                                  @*)
    (*@     gcoord.gpp.attach()                                                 @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 3 iNamed "Hgcoord". iNamed "Hts".
    wp_storeField.
    iNamed "Hgrd".
    wp_loadField.
    wp_apply (wp_GroupReader__reset with "[Hgrd]").
    { iNamed "Hgrd". iNamed "Hvaluem". iNamed "Hqreadm".
      by iFrame.
    }
    iIntros "Hgrd".
    iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_GroupPreparer__attach with "[Hgpp $Hcli]").
    { do 2 iNamed "Hgpp".
      iNamed "Hphase". iNamed "Hfrespm". iNamed "Hvdm". iNamed "Hsrespm".
      by iFrame.
    }
    iIntros "Hgpp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
