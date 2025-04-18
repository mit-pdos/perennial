From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Connect
    (gcoord : loc) (rid : u64) (addrm : gmap u64 chan) (addr : chan) gid γ :
    addrm !! rid = Some addr ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__Connect #gcoord #rid
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (Haddr) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Connect(rid uint64) bool {              @*)
    (*@     addr := gcoord.addrm[rid]                                           @*)
    (*@     ret := grove_ffi.Connect(addr)                                      @*)
    (*@     if !ret.Err {                                                       @*)
    (*@         gcoord.mu.Lock()                                                @*)
    (*@         gcoord.conns[rid] = ret.Connection                              @*)
    (*@         gcoord.mu.Unlock()                                              @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (addrpeer' ok) "[%Hok _]".
    destruct ok; last first.
    { apply map_get_false in Hok as [Hok _].
      by rewrite Haddr in Hok.
    }
    apply map_get_true in Hok.
    rewrite Haddr in Hok.
    symmetry in Hok. inv Hok.
    wp_pures.
    wp_apply wp_Connect.
    iIntros (err trml) "Htrml".
    wp_pures.
    wp_if_destruct.
    { wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      do 2 iNamed "Hgcoord". iNamed "Hcomm".
      wp_loadField.
      wp_apply (map.wp_MapInsert with "Hconns").
      iIntros "Hconns".
      wp_loadField.
      (* Seal [trml c↦ ∅] in the network invariant and obtain [is_terminal γ trml]. *)
      iApply ncfupd_wp.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iNamed "HinvnetO".
      iMod (terminal_update trml with "Hterminals") as "[Hterminals #Htrmlrcpt]".
      iMod ("HinvnetC" with "[$Hlistens Hconnects Hterminals Htrml]") as "_".
      { iModIntro.
        iExists (<[trml := ∅]> connects).
        rewrite dom_insert_L.
        iFrame "Hterminals %".
        iApply (big_sepM_insert_2 with "[Htrml] Hconnects").
        iExists ∅.
        iFrame.
        iSplit; first by rewrite big_sepS_empty.
        done.
      }
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $HconnsP $Hgcoord Hconns]").
      { iModIntro.
        iExists (<[rid := (trml, addr)]> conns).
        rewrite fmap_insert.
        iFrame "Hconns".
        iSplit.
        { by iApply big_sepM_insert_2. }
        iPureIntro.
        by apply map_Forall_insert_2.
      }
      wp_pures.
      by iApply "HΦ".
    }
    by iApply "HΦ".
  Qed.

End program.
