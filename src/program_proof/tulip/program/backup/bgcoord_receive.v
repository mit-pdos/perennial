From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Receive
    (gcoord : loc) (rid : u64) (addrm : gmap u64 chan) (addr : chan) rk ts gid γ :
    addrm !! rid = Some addr ->
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Receive #gcoord #rid
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

    (*@ func (gcoord *BackupGroupCoordinator) Receive(rid uint64) ([]byte, bool) { @*)
    (*@     conn, ok := gcoord.GetConnection(rid)                               @*)
    (*@     if !ok {                                                            @*)
    (*@         gcoord.Connect(rid)                                             @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     ret := grove_ffi.Receive(conn)                                      @*)
    (*@     if ret.Err {                                                        @*)
    (*@         gcoord.Connect(rid)                                             @*)
    (*@         return nil, false                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return ret.Data, true                                               @*)
    (*@ }                                                                       @*)
  Admitted.

End program.
