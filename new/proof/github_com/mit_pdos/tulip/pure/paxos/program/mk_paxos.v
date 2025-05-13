From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section mk_paxos.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_mkPaxos
    (nidme : u64) (termc : u64) (terml : u64) (lsnc : u64)
    (logP : Slice.t) (log : list byte_string) (addrmP : loc) (addrm : gmap u64 chan)
    (fname : byte_string) γ :
    (1 < size addrm)%nat ->
    nidme ∈ dom addrm ->
    0 ≤ uint.Z nidme < max_nodes ->
    is_node_wal_fname γ nidme fname -∗
    know_paxos_inv γ (dom addrm) -∗
    know_paxos_file_inv γ (dom addrm) -∗
    know_paxos_network_inv γ addrm -∗
    {{{ own_slice logP stringT (DfracOwn 1) log ∗
        own_map addrmP (DfracOwn 1) addrm ∗
        own_crash_ex pxcrashNS (own_paxos_durable γ nidme) (PaxosDurable termc terml log lsnc)
    }}}
      mkPaxos #nidme #termc #terml #lsnc (to_val logP) #addrmP #(LitString fname)
    {{{ (px : loc), RET #px; is_paxos_with_addrm px nidme addrm γ }}}.
  Proof.
    iIntros (Hmulti Hnidme Hltmax) "#Hfname #Hinv #Hinvfile #Hinvnet".
    (* avoid naming collision when opening invariant. *)
    iIntros (Φ) "!> (Hlog & Haddrm & Hdurable) HΦ".
    wp_rec.

    (*@ func mkPaxos(nidme, termc, terml, lsnc uint64, log []string, addrm map[uint64]grove_ffi.Address) *Paxos { @*)
    (*@     sc := uint64(len(addrm))                                            @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_MapLen with "Haddrm").
    iIntros "[%Hszaddrm Haddrm]".

    (*@     var peers = make([]uint64, 0, sc - 1)                               @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (peersP) "Hpeers".
    wp_apply wp_ref_to; first done.
    iIntros (peersPP) "HpeersPP".

    (*@     for nid := range(addrm) {                                           @*)
    (*@         if nid != nidme {                                               @*)
    (*@             peers = append(peers, nid)                                  @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    rewrite uint_nat_W64_0 /=.
    set P := (λ (m : gmap u64 u64), ∃ (peersP' : Slice.t) (peers' : list u64),
          "HpeersPP" ∷ peersPP ↦[slice.T uint64T] (to_val peersP') ∗
          "Hpeers"   ∷ own_slice peersP' uint64T (DfracOwn 1) peers' ∗
          "%Hpeers'" ∷ ⌜list_to_set peers' = dom m ∖ {[nidme]}⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Haddrm [$HpeersPP $Hpeers]").
    { rewrite dom_empty_L /=. iPureIntro. set_solver. }
    { clear Φ.
      iIntros (m nid addr Φ) "!> (HP & %Hnone & %Haddr) HΦ".
      iNamed "HP".
      wp_if_destruct.
      { wp_load.
        wp_apply (wp_SliceAppend with "Hpeers").
        iIntros (peersP'') "Hpeers".
        wp_store.
        iApply "HΦ".
        iFrame.
        iPureIntro.
        rewrite dom_insert_L list_to_set_app_L Hpeers' /=.
        set_solver.
      }
      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite dom_insert_L Hpeers'.
      clear -Hpeers'. set_solver.
    }
    iIntros "[Haddrm HP]".
    iNamed "HP". clear P.

    (*@     px := &Paxos{                                                       @*)
    (*@         nidme    : nidme,                                               @*)
    (*@         peers    : peers,                                               @*)
    (*@         addrm    : addrm,                                               @*)
    (*@         sc       : sc,                                                  @*)
    (*@         mu       : new(sync.Mutex),                                     @*)
    (*@         hb       : false,                                               @*)
    (*@         termc    : termc,                                               @*)
    (*@         terml    : terml,                                               @*)
    (*@         log      : log,                                                 @*)
    (*@         lsnc     : lsnc,                                                @*)
    (*@         iscand   : false,                                               @*)
    (*@         isleader : false,                                               @*)
    (*@         conns    : make(map[uint64]grove_ffi.Connection),               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
    wp_load.
    wp_apply (map.wp_NewMap).
    iIntros (conns) "Hconns".
    rewrite {1}/zero_val /=.
    wp_pures.
    wp_apply (wp_allocStruct).
    { by auto 25. }
    iIntros (px) "Hpx".
    wp_pures.
    iDestruct (struct_fields_split with "Hpx") as "Hpx".
    iNamed "Hpx".
    (* Make read-only persistent resources. *)
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iMod (readonly_alloc_1 with "cv") as "#HcvP".
    iMod (readonly_alloc_1 with "nidme") as "#HnidmeP".
    iMod (readonly_alloc_1 with "peers") as "#HpeersP".
    iDestruct (own_slice_to_small with "Hpeers") as "Hpeers".
    iMod (readonly_alloc_1 with "Hpeers") as "#Hpeers".
    iMod (readonly_alloc_1 with "addrm") as "#HaddrmP".
    iMod (readonly_alloc_1 with "fname") as "#HfnameP".
    iMod (own_map_persist with "Haddrm") as "#Haddrm".
    iAssert (own_paxos_comm px addrm γ)%I with "[$conns Hconns]" as "Hcomm".
    { iExists ∅.
      rewrite fmap_empty big_sepM_empty.
      by iFrame.
    }
    set nids := dom addrm.
    set logc := take (uint.nat lsnc) log.
    iAssert (own_paxos_candidate px nidme termc terml logc false nids γ)%I
      with "[$termp entsp $respp $iscand]" as "Hcand".
    { by iExists Slice.nil. }
    iAssert (own_paxos_leader px nidme termc terml log false nids γ)%I
      with "[$isleader $lsnpeers]" as "Hleader".
    iAssert (own_paxos_sc px nids)%I with "[$sc]" as "Hsc".
    { iPureIntro.
      split.
      { clear -Hmulti Hszaddrm. word. }
      { rewrite size_dom. clear -Hmulti Hszaddrm. word. }
    }
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamedSuffix "Hdurable" "X".
    (* Obtain persistent/pure resources that for convenience are also kept in lock inv. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iAssert (prefix_base_ledger γ (uint.nat terml) log)%I as "#Hgebase".
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hlogn.
      by iApply (big_sepM_lookup with "Hpsalbs").
    }
    iAssert (if decide (termc = terml)
             then True
             else past_nodedecs_latest_before γ nidme (uint.nat termc) (uint.nat terml) log)%I
      as "#Hpreped".
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (current_term_agree with "HtermcX Htermc") as %->.
      iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      case_decide as Hne; first done.
      iDestruct (past_nodedecs_witness with "Hds") as "#Hdslb".
      iFrame "Hdslb %".
      assert (Hlt : (uint.nat terml < uint.nat termc)%nat) by word.
      iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hlogn.
      iPureIntro.
      split.
      { rewrite /latest_term_nodedec Hlends.
        unshelve erewrite (fixed_proposals_latest_term_before_nodedec _ _ _ _ Hfixed).
        { lia. }
        apply free_terms_after_latest_term_before.
        { apply Hlt. }
        { clear -Hlogn. done. }
        { apply Hdompsa. }
      }
      { unshelve epose proof (list_lookup_lt ds (uint.nat terml) _) as [d Hd].
        { clear -Hlt Hlends. lia. }
        specialize (Hfixed _ _ Hd).
        rewrite Hd.
        rewrite Hfixed in Hlogn.
        f_equal.
        by apply nodedec_to_ledger_Some_inv.
      }
    }
    iAssert (is_accepted_proposal_lb γ nidme (uint.nat terml) log)%I as "#Hacpted".
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      iApply (accepted_proposal_witness with "Hacpt").
    }
    iAssert (safe_ledger_above γ nids (uint.nat terml) (take (uint.nat lsnc) log))%I
      as "#Hcmted".
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
      iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      iApply "Hsafel".
    }
    iAssert (⌜uint.Z terml ≤ uint.Z termc⌝)%I as %Htermlc.
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (current_term_agree with "HtermcX Htermc") as %->.
      iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
      iPureIntro.
      clear -Htermlc. word.
    }
    iAssert (⌜uint.Z lsnc ≤ length log⌝)%I as %Hlsncub.
    { iDestruct (paxos_inv_impl_node_inv nidme with "HinvO") as (terml') "Hnode"; first done.
      iNamed "Hnode".
      iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
      iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
      iPureIntro.
      clear -Hltlog. word.
    }
    iMod ("HinvC" with "HinvO") as "_".
    set dst := PaxosDurable termc terml log lsnc.
    iMod ("HdurableC" $! dst with "[$HtermcX $HtermlX $HlognX $HlsncX]") as "Hdurable".
    iAssert (own_paxos px nidme nids γ ∗ own_paxos_comm px addrm γ)%I
      with "[-HΦ Hfree]" as "(Hpx & Hcomm)".
    { iFrame "Hcand Hleader Hsc ∗ # %". }
    iMod (alloc_lock _ _ _ (own_paxos px nidme nids γ ∗ own_paxos_comm px addrm γ)
           with "Hfree [$Hpx $Hcomm]") as "#Hlock".

    (*@     return px                                                           @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    by iFrame "# %".
  Qed.

End mk_paxos.
