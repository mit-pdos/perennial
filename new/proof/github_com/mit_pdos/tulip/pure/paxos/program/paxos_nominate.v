From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import repr paxos_log.
From Perennial.program_proof.tulip.program.util Require Import next_aligned.
From Perennial.program_proof.tulip.paxos.invariance Require Import prepare.
From Goose.github_com.mit_pdos.tulip Require Import paxos util.

Section nominate.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_Paxos__nominate (px : loc) (nidme : u64) nids γ :
    nidme ∈ nids ->
    is_paxos_nids px nidme nids -∗
    is_paxos_fname px nidme γ -∗
    know_paxos_file_inv γ nids -∗
    know_paxos_inv γ nids -∗
    {{{ own_paxos px nidme nids γ }}}
      Paxos__nominate #px
    {{{ (term : u64) (lsn : u64), RET (#term, #lsn);
        own_paxos px nidme nids γ ∗ is_prepare_lsn γ (uint.nat term) (uint.nat lsn)
    }}}.
  Proof.
    iIntros (Hnidme) "#Hnids #Hfname #Hinvfile #Hinv".
    iIntros (Φ) "!> Hpx HΦ".
    wp_rec. wp_pures.

    (*@ func (px *Paxos) nominate() (uint64, uint64) {                          @*)
    (*@     // Compute the new term and proceed to that term.                   @*)
    (*@     term := util.NextAligned(px.termc, MAX_NODES, px.nid)               @*)
    (*@     px.termc = term                                                     @*)
    (*@     px.isleader = false                                                 @*)
    (*@                                                                         @*)
    do 2 iNamed "Hpx". iNamed "Hleader". iNamed "Hnids".
    do 2 wp_loadField.
    wp_apply wp_NextAligned.
    { word. }
    { rewrite /max_nodes in Hnid. word. }
    iIntros (term [Hgttermc Hmod]).
    do 2 wp_storeField.

    (*@     // Obtain entries after @px.lsnc.                                   @*)
    (*@     lsn := px.lsnc                                                      @*)
    (*@     ents := make([]string, uint64(len(px.log)) - lsn)                   @*)
    (*@     copy(ents, px.log[lsn :])                                           @*)
    (*@                                                                         @*)
    do 2 wp_loadField.
    wp_apply wp_slice_len.
    wp_apply wp_NewSlice.
    iIntros (entsP) "Hents".
    wp_loadField.
    iDestruct (own_slice_sz with "Hlog") as %Hsz.
    iDestruct (own_slice_small_acc with "Hlog") as "[Hlog HlogC]".
    iDestruct (own_slice_small_acc with "Hents") as "[Hents HentsC]".
    wp_apply (wp_SliceCopy_SliceSkip_src with "[$Hlog $Hents]").
    { word. }
    { rewrite length_replicate /=. word. }
    iIntros "[Hlog Hents]".
    iDestruct ("HlogC" with "Hlog") as "Hlog".
    iDestruct ("HentsC" with "Hents") as "Hents".

    (*@     // Use the candidate's log term (@px.terml) and entries (after the committed @*)
    (*@     // LSN, @ents) as the initial preparing term and entries.           @*)
    (*@     px.iscand = true                                                    @*)
    (*@     px.termp  = px.terml                                                @*)
    (*@     px.entsp  = ents                                                    @*)
    (*@     px.respp  = make(map[uint64]bool)                                   @*)
    (*@     px.respp[px.nidme] = true                                           @*)
    (*@                                                                         @*)
    iNamed "Hcand".
    wp_storeField.
    wp_loadField.
    do 2 wp_storeField.
    wp_apply (wp_NewMap u64 bool).
    iIntros (resppP') "Hrespp'".
    wp_storeField.
    do 2 wp_loadField.
    wp_apply (wp_MapInsert with "Hrespp'"); first done.
    iIntros "Hrespp'".
    wp_pures.

    (*@     // Logical action: Prepare(@term).                                  @*)
    (*@                                                                         @*)
    iNamed "Hfname".
    wp_loadField.
    wp_apply wp_logPrepare.
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    iInv "Hinv" as "> HinvO" "HinvC".
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hnodefile HinvfileO]".
    { apply Hnidme. }
    iNamed "Hnodefile".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iDestruct (node_wal_fname_agree with "Hfnameme Hwalfname") as %->.
    iFrame "Hfile %".
    iIntros (bs' failed) "Hfile".
    destruct failed.
    { (* Case: Write failed. Close the invariant without any updates. *)
      iMod "Hmask" as "_".
      iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
      { iFrame "∗ # %". }
      iMod ("HinvfileC" with "HinvfileO") as "_".
      iMod ("HinvC" with "HinvO") as "_".
      set dst := PaxosDurable termc terml log lsnc.
      iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
      by iIntros "!> %Hcontra".
    }
    (* Case: Write succeeded. *)
    iDestruct "Hfile" as "[Hfile %Hbs']".
    iMod (paxos_inv_prepare (uint.nat term) with "Hwalfile Htermc Hterml Hlogn HinvO")
      as "(Hwalfile & Htermc & Hterml & Hlogn & HinvO & Hlsnp & #Hpromise)".
    { apply Hnidme. }
    {  word. }
    destruct (decide (is_term_of_node nidme (uint.nat term))) as [Hton | Hnton]; last first.
    { exfalso. rewrite /is_term_of_node /max_nodes in Hnton. clear -Hmod Hnton. word. }
    set logc := take _ log.
    (* Set the prepare LSN to [length logc]. *)
    iMod (prepare_lsn_update (length logc) with "Hlsnp") as "#Hlsnprc".
    iDestruct ("HinvfileO" with "[Hfile Hwalfile]") as "HinvfileO".
    { iFrame "∗ # %".
      iPureIntro.
      apply Forall_app_2; first apply Hvdwal.
      rewrite Forall_singleton /=.
      word.
    }
    iMod "Hmask" as "_".
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HinvC" with "HinvO") as "_".
    set dst := PaxosDurable term terml log lsnc.
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iIntros "!> _".
    wp_pures.

    (*@     return term, lsn                                                    @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    assert (Hton' : is_term_of_node nidme (uint.nat term)).
    { rewrite /is_term_of_node /max_nodes. word. }
    assert (Htermlt' : uint.Z terml ≤ uint.Z term) by word.
    assert (Hlcne' : uint.Z terml ≠ uint.Z term) by word.
    set entsp := drop _ log.
    set respp' := map_insert _ _ _.
    iAssert (votes_in γ (dom respp') (uint.nat term) (uint.nat terml) (logc ++ entsp))%I as "Hvotes".
    { iNamed "Hpromise".
      iExists {[nidme := ds]}.
      rewrite big_sepM_singleton.
      iFrame "Hpastd".
      iPureIntro.
      split.
      { rewrite map_Forall_singleton. clear -Hlends Htermlt'. word. }
      split.
      { apply latest_term_before_quorum_with_singleton.
        by rewrite -latest_term_before_nodedec_unfold -Hlends -latest_term_nodedec_unfold.
      }
      split.
      { apply length_of_longest_ledger_in_term_singleton.
        by rewrite Hacpt take_drop.
      }
      split.
      { by rewrite map_Exists_singleton Hacpt take_drop. }
      { rewrite dom_singleton_L dom_insert_L. set_solver. }
    }
    iModIntro.
    iSplit; last first.
    { rewrite length_take_le; last first.
      { clear -Hlsncub. lia. }
      iFrame "Hlsnprc".
    }
    iFrame "HiscandP HisleaderP".
    iFrame "∗ # %".
    iSplit.
    { iClear "Hpreped". by case_decide. }
    iPureIntro.
    split; last lia.
    rewrite dom_insert_L. set_solver.
  Qed.

End nominate.
