From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__GetConnection
    (gcoord : loc) (rid : u64) (addrm : gmap u64 chan) (addr : chan) gid γ :
    addrm !! rid = Some addr ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__GetConnection #gcoord #rid
    {{{ (trml : chan) (ok : bool), RET (if ok 
                                     then (connection_socket trml addr, #true)
                                     else (#(), #false));
        if ok then is_terminal γ gid trml else True
    }}}.
  Proof.
    iIntros (Haddr) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) GetConnection(rid uint64) (grove_ffi.Connection, bool) { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     conn, ok := gcoord.conns[rid]                                       @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return conn, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    do 2 iNamed "Hgcoord".
    iNamed "Hcomm".
    wp_loadField.
    wp_apply (map.wp_MapGet with "Hconns").
    iIntros (connV ok) "[%Hok Hconns]".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". iFrame "Hgcoord ∗ # %". }
    wp_pures.
    destruct ok; last first.
    { apply map.map_get_false in Hok as [_ ->].
      (* [U64 0] is a placeholder *)
      by iApply ("HΦ" $! (U64 0) false).
    }
    apply map.map_get_true in Hok.
    rewrite lookup_fmap_Some in Hok.
    destruct Hok as ([trml addr'] & <- & Hconns).
    iDestruct (big_sepM_lookup with "Htrmls") as "Htrml"; first apply Hconns.
    apply Haddrm in Hconns.
    rewrite Haddr in Hconns.
    symmetry in Hconns. inv Hconns.
    by iApply ("HΦ" $! _ true).
  Qed.

End program.
