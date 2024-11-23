From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_prepare_session gcoord_wait_until_prepare_done.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Prepare
    (gcoord : loc) (tsW : u64) (ptgsP : Slice.t) (pwrsP : loc) gid γ :
    let ts := uint.nat tsW in
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Prepare #gcoord #tsW (to_val ptgsP) #pwrsP
    {{{ (phase : txnphase) (valid : bool), RET (#(txnphase_to_u64 phase), #valid); 
        if valid then safe_group_txnphase γ ts gid phase else True
    }}}.
  Proof.
    iIntros (ts) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Prepare(ts uint64, ptgs []uint64, pwrs tulip.KVMap) (uint64, bool) { @*)
    (*@     // Spawn a prepare session with each replica.                       @*)
    (*@     for ridloop := range(gcoord.addrm) {                                  @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.PrepareSession(rid, ts, ptgs, pwrs)                  @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hgcoord" as "Hgcoord'".
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    iRename "Hgcoord'" into "Hgcoord".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> _ HΦ".
      wp_pures.
      wp_apply wp_fork.
      { by wp_apply (wp_GroupCoordinator__PrepareSession with "Hgcoord"). }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     st, valid := gcoord.WaitUntilPrepareDone(ts)                        @*)
    (*@     return st, valid                                                    @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupCoordinator__WaitUntilPrepareDone with "Hgcoord").
    iIntros (phase valid) "#Hsafep".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
