From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr resume mk_paxos paxos_serve
  paxos_leader_session paxos_election_session paxos_response_session
  paxos_heartbeat_session.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section start.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Start
    (nidme : u64) (termc : u64) (terml : u64) (lsnc : u64) (log : list byte_string)
    (addrmP : loc) (addrm : gmap u64 chan) (fname : byte_string) γ :
    termc = (W64 0) ->
    terml = (W64 0) ->
    lsnc = (W64 0) ->
    log = [] ->
    (* remove above assumptions once recovery is proven *)
    is_node_wal_fname γ nidme fname -∗
    know_paxos_inv γ (dom addrm) -∗
    know_paxos_file_inv γ (dom addrm) -∗
    know_paxos_network_inv γ addrm -∗
    {{{ own_map addrmP (DfracOwn 1) addrm ∗
        own_current_term_half γ nidme (uint.nat termc) ∗
        own_ledger_term_half γ nidme (uint.nat terml) ∗
        own_committed_lsn_half γ nidme (uint.nat lsnc) ∗
        own_node_ledger_half γ nidme log
    }}}
      Start #nidme #addrmP #(LitString fname)
    {{{ (px : loc), RET #px; is_paxos px nidme γ }}}.
  Proof.
    iIntros (Htermcz Htermlz Hlsncz Hlogz).
    iIntros "#Hfnamewal #Hinv #Hinvfile #Hinvnet" (Φ).
    iIntros "!> (Haddrm & Htermc & Hterml & Hlsnc & Hlogn) HΦ".
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
    wp_pures.
    wp_apply wp_NewSlice.
    iIntros (logP) "Hlog".
    rewrite uint_nat_W64_0 replicate_0.
    rewrite Htermcz Htermlz Hlsncz Hlogz.
    (* wp_apply (wp_resume with "[$Htermc $Hterml $Hlsnc $Hlogn]"). *)
    (* iIntros (logP) "(Htermc & Hterml & Hlsnc & Hlogn & Hlog)". *)

    (*@     px := mkPaxos(nidme, termc, terml, lsnc, log, addrm)                @*)
    (*@                                                                         @*)
    wp_apply (wp_mkPaxos
               with "Hfnamewal Hinv Hinvfile Hinvnet [$Hlog $Haddrm $Htermc $Hterml $Hlsnc $Hlogn]").
    { clear -Hmulti. word. }
    { by apply elem_of_dom. }
    { clear -Hltmax. rewrite /max_nodes. word. }
    iIntros (px) "#Hpx".
    iClear "Hinv Hinvnet".

    (*@     go func() {                                                         @*)
    (*@         px.Serve()                                                      @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { wp_apply (wp_Paxos__Serve with "[Hpx]").
      { iNamed "Hpx". iFrame "# %". }
      done.
    }

    (*@     go func() {                                                         @*)
    (*@         px.LeaderSession()                                              @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { wp_apply (wp_Paxos__LeaderSession with "[Hpx]").
      { iNamed "Hpx". iFrame "# %". }
      done.
    }

    wp_apply wp_fork.
    { wp_apply (wp_Paxos__HeartbeatSession with "[Hpx]").
      { iNamed "Hpx". iFrame "# %". }
      done.
    }

    (*@     go func() {                                                         @*)
    (*@         px.ElectionSession()                                            @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { wp_apply (wp_Paxos__ElectionSession with "[Hpx]").
      { iNamed "Hpx". iFrame "# %". }
      done.
    }

    (*@     for _, nidloop := range(px.peers) {                                 @*)
    (*@         nid := nidloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             px.ResponseSession(nid)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iAssert (is_paxos_nids px nidme (dom addrm))%I as "Hnids".
    { by iNamed "Hpx". }
    iNamed "Hnids".
    iMod (readonly_load with "Hpeers") as (q) "HpeersR".
    wp_loadField.
    wp_apply (wp_forSlice (λ _, True)%I with "[] [$HpeersR]").
    { clear Φ.
      iIntros (i nid Φ) "!> %Hiter HΦ".
      destruct Hiter as (_ & Hbound & Hnid).
      wp_apply wp_fork.
      { assert (is_Some (addrm !! nid)) as [addr Haddr].
        { apply elem_of_list_lookup_2 in Hnid.
          rewrite -elem_of_dom.
          set_solver.
        }
        wp_apply (wp_Paxos__ResponseSession with "Hpx"); first apply Haddr.
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     return px                                                           @*)
    (*@ }                                                                       @*)
    wp_pures.
    iApply "HΦ".
    iNamed "Hpx".
    by iFrame "# %".
  Qed.

End start.
