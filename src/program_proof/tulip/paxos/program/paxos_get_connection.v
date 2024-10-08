From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section get_connection.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__GetConnection
    (px : loc) (nid : u64) (nidme : u64) (addrm : gmap u64 chan) (addrpeer : chan) γ :
    addrm !! nid = Some addrpeer ->
    is_paxos_with_addrm px nidme addrm γ -∗
    {{{ True }}}
      Paxos__GetConnection #px #nid
    {{{ (trml : chan) (ok : bool), RET (if ok 
                                     then (connection_socket trml addrpeer, #true)
                                     else (#(), #false));
        if ok then is_terminal γ trml else True
    }}}.
  Proof.
    iIntros (Haddrpeer) "#Hpx".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (px *Paxos) GetConnection(nid uint64) (grove_ffi.Connection, bool) { @*)
    (*@     px.mu.Lock()                                                        @*)
    (*@     conn, ok := px.conns[nid]                                           @*)
    (*@     px.mu.Unlock()                                                      @*)
    (*@     return conn, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hpx".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked [Hpx Hcomm]]".
    iNamed "Hcomm".
    wp_loadField.
    wp_apply (map.wp_MapGet with "Hconns").
    iIntros (connV ok) "[%Hok Hconns]".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { iFrame "Hlock Hlocked". iFrame "Hpx ∗ # %". }
    wp_pures.
    destruct ok; last first.
    { apply map.map_get_false in Hok as [_ ->].
      (* [U64 0] is a placeholder *)
      by iApply ("HΦ" $! (U64 0) false).
    }
    apply map.map_get_true in Hok.
    rewrite lookup_fmap_Some in Hok.
    destruct Hok as ([trml addrpeer'] & <- & Hconns).
    iDestruct (big_sepM_lookup with "Htrmls") as "Htrml"; first apply Hconns.
    apply Haddrpeers in Hconns.
    rewrite Haddrpeer in Hconns.
    symmetry in Hconns. inv Hconns.
    by iApply ("HΦ" $! _ true).
  Qed.

End get_connection.
