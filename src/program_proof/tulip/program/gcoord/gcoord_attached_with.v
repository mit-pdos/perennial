From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__attachedWith (gcoord : loc) (tsW : u64) tscur rids gid γ :
    let ts := uint.nat tsW in
    {{{ own_gcoord_core gcoord tscur gid rids γ }}}
      GroupCoordinator__attachedWith #gcoord #tsW
    {{{ (ok : bool), RET #ok;
        if ok
        then own_gcoord_core gcoord ts gid rids γ
        else own_gcoord_core gcoord tscur gid rids γ
    }}}.
  Proof.
    iIntros (ts Φ) "Hgcoord HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) attachedWith(ts uint64) bool {          @*)
    (*@     return gcoord.ts == ts                                              @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord".
    rename tsW into tsargW. iNamed "Hts".
    wp_loadField.
    wp_pures.
    case_bool_decide as Htsarg.
    { iApply "HΦ". inv Htsarg. by iFrame "∗ # %". }
    { iApply "HΦ". by iFrame "∗ # %". }
  Qed.

  Theorem wp_GroupCoordinator__AttachedWith (gcoord : loc) (ts : u64) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__AttachedWith #gcoord #ts
    {{{ (attached : bool), RET #attached; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) AttachedWith(ts uint64) bool {          @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     b := gcoord.attachedWith(ts)                                        @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return b                                                            @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 2 iNamed "Hgcoord".
    wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
    iIntros (b) "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". by destruct b; iFrame. }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
