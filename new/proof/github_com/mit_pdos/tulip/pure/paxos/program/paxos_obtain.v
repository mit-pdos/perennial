From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section obtain.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__obtain (px : loc) (nid : u64) (nidme termc : u64) nids γ :
    {{{ own_paxos_leading_with_termc px nidme termc nids γ }}}
      Paxos__obtain #px #nid
    {{{ (lsne : u64) (entsP : Slice.t) (ents loga : list byte_string), RET (#lsne, (to_val entsP));
        own_paxos_leading_with_termc px nidme termc nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents ∗
        prefix_base_ledger γ (uint.nat termc) loga ∗
        prefix_growing_ledger γ (uint.nat termc) loga ∗
        ⌜(uint.nat lsne ≤ length loga)%nat⌝ ∗
        ⌜drop (uint.nat lsne) loga = ents⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) obtain(nid uint64) (uint64, []string) {                @*)
    (*@     lsne, ok := px.lsnpeers[nid]                                        @*)
    (*@                                                                         @*)
    iNamed "Hpx". iNamed "Hleader". iNamed "Honlyl".
    wp_loadField.
    wp_apply (wp_MapGet with "Hlsnpeers").
    iIntros (lsne ok) "[%Hok Hlsnpeers]".
    wp_pures.

    (*@     if !ok {                                                            @*)
    (*@         // The follower has not reported the matched LSN, so send an    @*)
    (*@         // empty APPEND-ENTRIES request.                                @*)
    (*@         return uint64(len(px.log)), make([]string, 0)                   @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iAssert (prefix_growing_ledger γ (uint.nat termc) log)%I as "#Hpfg".
    { iDestruct (proposal_witness with "Hps") as "#Hpslb".
      by iFrame "Hpslb".
    }
    iNamed "Hpx".
    iDestruct (own_slice_sz with "Hlog") as %Hszlog.
    wp_if_destruct.
    { wp_loadField.
      wp_apply wp_slice_len.
      wp_apply wp_NewSlice.
      iIntros (entsP) "Hents".
      wp_pures.
      iApply "HΦ".
      iFrame "Hcand".
      iFrame "∗ # %".
      iPureIntro.
      by rewrite -Hszlog drop_all uint_nat_W64_0 /=.
    }
    apply map_get_true in Hok.
    apply Hlelog in Hok.

    (*@     // The follower has reported up to where the log is matched         @*)
    (*@     // (i.e., @lsne), so send everything after that.                    @*)
    (*@     ents := make([]string, uint64(len(px.log)) - lsne)                  @*)
    (*@     copy(ents, px.log[lsne :])                                          @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    iDestruct (own_slice_sz with "Hents") as %Hszents.
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { clear -Hok. word. }
    { rewrite length_replicate. clear -Hszents Hszlog Hok. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".
    wp_pures.

    (*@     return lsne, ents                                                   @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "Hcand".
    by iFrame "∗ # %".
  Qed.

End obtain.
