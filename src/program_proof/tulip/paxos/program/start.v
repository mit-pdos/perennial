From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr resume mk_paxos paxos_serve
  paxos_leader_session paxos_election_session paxos_response_session.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section start.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Start
    (nidme : u64) (termc : u64) (terml : u64) (lsnc : u64) (log : list string)
    (addrmP : loc) (addrm : gmap u64 chan) nids γ :
    dom addrm = nids ->
    know_paxos_inv γ nids -∗
    know_paxos_network_inv γ nids addrm -∗
    {{{ own_map addrmP (DfracOwn 1) addrm ∗
        own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log
    }}}
      Start #nidme #addrmP
    {{{ (px : loc), RET #px; is_paxos px nidme γ }}}.
  Proof.
    iIntros (Hdomaddrm) "#Hinv #Hinvnet".
    iIntros (Φ) "!> (Haddrm & Htermc & Hterml & Hlsnc & Hlogn) HΦ".
    wp_rec.

    (*@ func Start(nidme uint64, addrm map[uint64]grove_ffi.Address) *Paxos {   @*)
    (*@     // Check that the cluster has more than one node.                   @*)
    (*@     primitive.Assume(1 < uint64(len(addrm)))                            @*)
    (*@                                                                         @*)
    wp_apply (wp_MapLen with "Haddrm").
    iIntros "[%Hszaddrm Haddrm]".
    wp_apply wp_Assume.
    iIntros (Hmulti).
    rewrite bool_decide_eq_true in Hmulti.

    (*@     // Check that @nidme is part of the cluster.                        @*)
    (*@     _, ok := addrm[nidme]                                               @*)
    (*@     primitive.Assume(ok)                                                @*)
    (*@                                                                         @*)
    wp_apply (wp_MapGet with "Haddrm").
    iIntros (chan ok) "[%Hinnids Haddrm]".
    wp_apply wp_Assume.
    iIntros (->).
    apply map_get_true in Hinnids.

    (*@     // Check the @nidme is valid.                                       @*)
    (*@     primitive.Assume(nidme < MAX_NODES)                                 @*)
    (*@                                                                         @*)
    wp_apply wp_Assume.
    iIntros (Hltmax).
    rewrite bool_decide_eq_true in Hltmax.

    (*@     termc, terml, lsnc, log := resume()                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_resume with "[$Htermc $Hterml $Hlsnc $Hlogn]").
    iIntros (logP) "(Htermc & Hterml & Hlsnc & Hlogn & Hlog)".

    (*@     px := mkPaxos(nidme, termc, terml, lsnc, log, addrm)                @*)
    (*@                                                                         @*)
    wp_apply (wp_mkPaxos with "Hinv Hinvnet [$Hlog $Haddrm $Htermc $Hterml $Hlsnc $Hlogn]").
    { rewrite -Hdomaddrm size_dom. clear -Hmulti. word. }
    { apply Hdomaddrm. }
    { apply elem_of_dom_2 in Hinnids. by rewrite Hdomaddrm in Hinnids. }
    { clear -Hltmax. rewrite /max_nodes. word. }
    iIntros (px) "#Hpx".

    (*@     go func() {                                                         @*)
    (*@         px.Serve()                                                      @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Paxos__Serve with "Hpx"). }

    (*@     go func() {                                                         @*)
    (*@         px.LeaderSession()                                              @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Paxos__LeaderSession with "Hpx"). }

    (*@     go func() {                                                         @*)
    (*@         px.ElectionSession()                                            @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Paxos__ElectionSession with "Hpx"). }

    (*@     for _, nidloop := range(px.peers) {                                 @*)
    (*@         nid := nidloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             px.ResponseSession(nid)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)

    (*@     return px                                                           @*)
    (*@ }                                                                       @*)
  Admitted.

End start.
