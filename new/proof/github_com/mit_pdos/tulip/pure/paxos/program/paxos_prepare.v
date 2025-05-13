From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section prepare.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__prepare (px : loc) (lsn : u64) (nidme termc terml : u64) nids γ :
    termc ≠ terml ->
    {{{ own_paxos_with_termc_terml px nidme termc terml nids γ }}}
      Paxos__prepare #px #lsn
    {{{ (entsP : Slice.t) (ents logpeer : list byte_string), RET (#terml, (to_val entsP));
        own_paxos_with_termc_terml px nidme termc terml nids γ ∗
        own_slice entsP stringT (DfracOwn 1) ents ∗
        past_nodedecs_latest_before γ nidme (uint.nat termc) (uint.nat terml) logpeer ∗
        ⌜drop (uint.nat lsn) logpeer = ents⌝
    }}}.
  Proof.
    iIntros (Hne Φ) "Hpx HΦ".
    wp_rec.

    (*@ func (px *Paxos) prepare(lsn uint64) (uint64, []string) {               @*)
    (*@     if uint64(len(px.log)) <= lsn {                                     @*)
    (*@         return px.terml, make([]string, 0)                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx".
    case_decide; first done.
    wp_loadField.
    iDestruct (own_slice_sz with "Hlog") as %Hsz.
    wp_apply wp_slice_len.
    wp_if_destruct.
    { wp_loadField.
      wp_apply wp_NewSlice.
      iIntros (entsP) "Hents".
      wp_pures.
      iApply "HΦ".
      iFrame "Hcand Hleader".
      iFrame "∗ # %".
      case_decide; first done.
      iFrame "Hpreped".
      iPureIntro.
      rewrite uint_nat_W64_0 drop_ge /=; [done | lia].
    }

    (*@     ents := make([]string, uint64(len(px.log)) - lsn)                   @*)
    (*@     copy(ents, px.log[lsn :])                                           @*)
    (*@     return px.terml, ents                                               @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    wp_loadField.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { word. }
    { rewrite length_replicate /=. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    iFrame "Hcand Hleader".
    iFrame "∗ # %".
    case_decide; first done.
    by iFrame "Hpreped".
  Qed.

End prepare.
