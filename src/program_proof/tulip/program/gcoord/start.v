From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr mk_gcoord gcoord_response_session gcoord_resend_session.
From Goose.github_com.mit_pdos.tulip Require Export gcoord.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Start (addrmP : loc) (addrm : gmap u64 chan) gid γ :
    gid ∈ gids_all ->
    dom addrm = rids_all ->
    own_map addrmP DfracDiscarded addrm -∗
    know_tulip_inv γ -∗
    know_tulip_network_inv γ gid addrm -∗
    {{{ True }}}
      Start #addrmP
    {{{ (gcoord : loc), RET #gcoord; is_gcoord gcoord gid γ }}}.
  Proof.
    iIntros (Hgid Hdomaddrm) "#Haddrm #Hinv #Hinvnet".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func Start(addrm map[uint64]grove_ffi.Address) *GroupCoordinator {      @*)
    (*@     gcoord := mkGroupCoordinator(addrm)                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_mkGroupCoordinator with "Haddrm Hinv Hinvnet").
    { apply Hgid. }
    { apply Hdomaddrm. }
    iIntros (gcoord) "#Hgcoord".

    (*@     for ridloop := range(addrm) {                                       @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.ResponseSession(rid)                                 @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_MapIter_fold _ _ _ (λ _ : gmap u64 chan, True)%I with "Haddrm []"); first done.
    { clear Φ.
      iIntros (m rid addr Φ) "!> [_ [_ %Haddr]] HΦ".
      wp_apply wp_fork; last by iApply "HΦ".
      wp_apply (wp_GroupCoordinator__ResponseSession with "Hgcoord").
      { apply Haddr. }
      done.
    }
    iIntros "_".

    (*@     go func() {                                                         @*)
    (*@         gcoord.ResendSession()                                          @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { wp_apply (wp_GroupCoordinator__ResendSession).
      { by iFrame "Hgcoord". }
      done.
    }

    (*@     return gcoord                                                       @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    by iFrame "Hgcoord".
  Qed.

End program.
