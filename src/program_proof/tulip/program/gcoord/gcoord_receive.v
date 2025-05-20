From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_get_connection gcoord_connect.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__Receive
    (gcoord : loc) (rid : u64) (addrm : gmap u64 chan) (addr : chan) gid γ :
    addrm !! rid = Some addr ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__Receive #gcoord #rid
    {{{ (dataP : Slice.t) (ok : bool), RET (to_val dataP, #ok);
        if ok
        then ∃ (data : list u8) (resp : txnresp),
            own_slice dataP byteT (DfracOwn 1) data ∗
            safe_txnresp γ gid resp ∗
            ⌜encode_txnresp resp data⌝
        else True
    }}}.
  Proof.
    iIntros (Haddr) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) Receive(rid uint64) ([]byte, bool) {    @*)
    (*@     conn, ok := gcoord.GetConnection(rid)                               @*)
    (*@     if !ok {                                                            @*)
    (*@         gcoord.Connect(rid)                                             @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__GetConnection with "[Hpx]").
    { apply Haddr. }
    { iFrame "#". }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_GroupCoordinator__Connect with "[Hpx]").
      { apply Haddr. }
      { iFrame "#". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     ret := grove_ffi.Receive(conn)                                      @*)
    (*@     if ret.Err {                                                        @*)
    (*@         gcoord.Connect(rid)                                             @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_Receive.
    iNamed "Hpx".
    iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iNamed "HinvnetO".
    iDestruct (terminal_lookup with "Htrmlrcpt Hterminals") as %Htrml.
    apply elem_of_dom in Htrml as [ms Hms].
    iDestruct (big_sepM_lookup_acc with "Hconnects") as "[Htrml HconnectsC]".
    { apply Hms. }
    iNamed "Htrml".
    iFrame "Hms".
    iIntros (err data) "[Hms Hmsg]".
    iDestruct ("HconnectsC" with "[$Hms]") as "Hconnects"; first iFrame "# %".
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_"; first done.
    iIntros "!>" (dataP) "Hdata".
    wp_pures.
    destruct err; wp_pures.
    { wp_apply (wp_GroupCoordinator__Connect with "[]").
      { apply Haddr. }
      { by iFrame "HcvP #". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     return ret.Data, true                                               @*)
    (*@ }                                                                       @*)
    iDestruct "Hmsg" as %Hmsg.
    specialize (Henc _ Hmsg). simpl in Henc.
    destruct Henc as (resp & Hinresps & Hresp).
    iDestruct (big_sepS_elem_of with "Hresps") as "Hresp"; first apply Hinresps.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
