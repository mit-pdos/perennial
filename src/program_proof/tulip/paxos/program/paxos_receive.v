From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_get_connection paxos_connect.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section receive.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__Receive
    (px : loc) (nid : u64) (nidme : u64)
    (addrpeer : chan) (addrm : gmap u64 chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__Receive #px #nid
    {{{ (dataP : Slice.t) (ok : bool), RET (to_val dataP, #ok);
        if ok
        then ∃ (data : list u8) (resp : pxresp),
            own_slice dataP byteT (DfracOwn 1) data ∗
            safe_pxresp γ (dom addrm) resp ∗
            ⌜data = encode_pxresp resp⌝
        else True
    }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) Receive(nid uint64) ([]byte, bool) {                   @*)
    (*@     conn, ok := px.GetConnection(nid)                                   @*)
    (*@     if !ok {                                                            @*)
    (*@         px.Connect(nid)                                                 @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Paxos__GetConnection with "[Hpx]").
    { apply Haddrpeer. }
    { iFrame "#". }
    iIntros (trml ok) "#Htrmlrcpt".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply (wp_Paxos__Connect with "[Hpx]").
      { apply Haddrpeer. }
      { iFrame "#". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     ret := grove_ffi.Receive(conn)                                      @*)
    (*@     if ret.Err {                                                        @*)
    (*@         px.Connect(nid)                                                 @*)
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
    { wp_apply (wp_Paxos__Connect with "[]").
      { apply Haddrpeer. }
      { by iFrame "#". }
      iIntros (ok) "Hok".
      wp_pures.
      by iApply ("HΦ" $! Slice.nil false).
    }

    (*@     return ret.Data, true                                               @*)
    (*@ }                                                                       @*)
    iDestruct "Hmsg" as %Hmsg.
    assert (∃ resp, data = encode_pxresp resp ∧ resp ∈ resps) as (resp & Hresp & Hinresps).
    { specialize (Henc data).
      apply (elem_of_map_2 msg_data (D := gset (list u8))) in Hmsg.
      specialize (Henc Hmsg).
      by rewrite elem_of_map in Henc.
    }
    iDestruct (big_sepS_elem_of with "Hresps") as "Hresp"; first apply Hinresps.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End receive.
