From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_prepare_session gcoord_wait_until_prepare_done.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Prepare
    (gcoord : loc) (tsW : u64) (pwrsP : loc) (ptgsP : Slice.t)
    (pwrs : dbmap) (ptgs : txnptgs) gid γ :
    let ts := uint.nat tsW in
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    own_map pwrsP DfracDiscarded pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Prepare #gcoord #tsW (to_val ptgsP) #pwrsP
    {{{ (phase : txnphase) (valid : bool), RET (#(txnphase_to_u64 phase), #valid); 
        if valid then safe_group_txnphase γ ts gid phase else True
    }}}.
  Proof.
    iIntros (ts) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hgcoord".
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
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> [_ %Hrid] HΦ".
      destruct Hrid as [_ Hrid].
      wp_pures.
      iAssert (is_gcoord_with_addrm gcoord gid addrm γ)%I as "#Hgcoord".
      { iFrame "HcvP # %". }
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__PrepareSession
                   with "Hlnrz Hsafepwrs Hsafeptgs Hpwrs Hptgs Hgcoord").
        { by apply elem_of_dom_2 in Hrid. }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     st, valid := gcoord.WaitUntilPrepareDone(ts)                        @*)
    (*@     return st, valid                                                    @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupCoordinator__WaitUntilPrepareDone).
    { by iFrame "HcvP # %". }
    iIntros (phase valid) "#Hsafep".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
