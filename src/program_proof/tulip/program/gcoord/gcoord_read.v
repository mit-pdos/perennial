From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_read_session gcoord_wait_until_value_ready.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Read
    (gcoord : loc) (tsW : u64) (key : byte_string) gid γ :
    let ts := uint.nat tsW in
    safe_read_req gid ts key ->
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__Read #gcoord #tsW #(LitString key)
    {{{ (value : dbval) (ok : bool), RET (dbval_to_val value, #ok); 
        if ok then fast_or_quorum_read γ key ts value else True
    }}}.
  Proof.
    iIntros (ts Hsafe) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Read(ts uint64, key string) (tulip.Value, bool) { @*)
    (*@     // Spawn a session with each replica in the group.                  @*)
    (*@     for ridloop := range(gcoord.addrm) {                                  @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.ReadSession(rid, ts, key)                            @*)
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
      iIntros (mx rid c Φ) "!> [_ %Hrid] HΦ".
      wp_pures.
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__ReadSession with "Hgcoord").
        { destruct Hrid as [_ Hrid].
          apply elem_of_dom_2 in Hrid.
          by rewrite -Hrps -Hdomaddrm.
        }
        { apply Hsafe. }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     v, ok := gcoord.WaitUntilValueReady(ts, key)                        @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupCoordinator__WaitUntilValueReady with "Hgcoord").
    iIntros (v ok) "#Hread".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
