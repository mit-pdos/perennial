From Perennial.program_proof.tulip.program Require Import prelude.
(* FIXME: adhoc fix to name collision, fix a global import in program prelude *)
From Goose.github_com.mit_pdos.tulip Require Export backup.
From Perennial.program_proof.tulip.program.backup Require Import
  btcoord_repr bgcoord_repr start_bgcoord.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Start
    (tsW : u64) (rkW : u64) (cid : coordid) (ptgsP : Slice.t)
    (gaddrmPP : loc) (gaddrmP : gmap u64 loc) (leader : u64) (proph : proph_id)
    (ptgs : txnptgs) (gaddrm : gmap u64 (gmap u64 chan)) γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    (1 < rk)%nat ->
    dom gaddrm = gids_all ->
    map_Forall (λ _ addrm, dom addrm = rids_all) gaddrm ->
    is_lnrz_tid γ ts -∗
    safe_backup_txn γ ts ptgs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    own_map gaddrmPP DfracDiscarded gaddrmP -∗
    ([∗ map] addrmP; addrm ∈ gaddrmP; gaddrm, own_map addrmP DfracDiscarded addrm) -∗
    know_tulip_inv_with_proph γ proph -∗
    ([∗ map] gid ↦ addrm ∈ gaddrm, know_tulip_network_inv γ gid addrm) -∗
    {{{ ([∗ set] gid ∈ gids_all, own_replica_backup_token γ cid.1 cid.2 ts rk gid) }}}
      Start #tsW #rkW (coordid_to_val cid) (to_val ptgsP) #gaddrmPP #leader #proph
    {{{ (tcoord : loc), RET #tcoord; own_backup_tcoord tcoord ts γ }}}.
  Proof.
    iIntros (ts rk Hrk Hgids Hrids) "#Hlnrzed #Hsafebk #Hptgs #HgaddrmP #Hgaddrm #Hinv #Hinvnets".
    iIntros (Φ) "!> Htokens HΦ".
    wp_rec.

    (*@ func Start(ts, rank uint64, cid tulip.CoordID, ptgs []uint64, gaddrm tulip.AddressMaps, leader uint64, proph primitive.ProphId) *BackupTxnCoordinator { @*)
    (*@     gcoords := make(map[uint64]*BackupGroupCoordinator)                 @*)
    (*@                                                                         @*)
    wp_apply (wp_NewMap).
    iIntros (gcoordsPP) "HgcoordsP".

    (*@     // Create a backup group coordinator for each participant group.    @*)
    (*@     for _, gid := range(ptgs) {                                         @*)
    (*@         addrm := gaddrm[gid]                                            @*)
    (*@         gcoord := startBackupGroupCoordinator(addrm, cid, ts, rank)     @*)
    (*@         gcoords[gid] = gcoord                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hsafebk".
    iDestruct "Hptgs" as (ptgsL) "(#HptgsL & %HptgsL & %Hnd)".
    set P := (λ (i : u64),
                ∃ (gcoords : gmap u64 loc),
                  "HgcoordsP" ∷ own_map gcoordsPP (DfracOwn 1) gcoords ∗
                  "Hgcoords" ∷ ([∗ map] gid ↦ gcoord ∈ gcoords,
                                  is_backup_gcoord gcoord rk ts gid γ) ∗
                  "Htks" ∷ ([∗ set] gid ∈ list_to_set (drop (uint.nat i) ptgsL),
                              own_replica_backup_token γ cid.1 cid.2 ts rk gid) ∗
                  "%Hdomgc" ∷ ⌜dom gcoords = list_to_set (take (uint.nat i) ptgsL)⌝)%I.
    iDestruct (own_slice_small_sz with "HptgsL") as %Hlenptgs.
    wp_apply (wp_forSlice P with "[] [$HptgsL $HgcoordsP Htokens]"); last first; first 1 last.
    { rewrite uint_nat_W64_0 drop_0 take_0 HptgsL dom_empty_L /=.
      iSplit; first by iApply big_sepM_empty.
      iSplit; last done.
      iApply (big_sepS_subseteq with "Htokens").
      rewrite Hvptgs.
      apply subseteq_ptgroups.
    }
    { clear Φ.
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP".
      wp_pures.
      wp_apply (wp_MapGet with "HgaddrmP").
      iIntros (addrmP ok) "[%Hok HaddrmP]".
      wp_pures.
      assert (Hinptgs : gid ∈ ptgs).
      { apply list_elem_of_lookup_2 in Hgid.
        clear -Hgid HptgsL.
        set_solver.
      }
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        rewrite -Hvptgs in Hdom.
        clear -Hdom Hinptgs.
        set_solver.
      }
      iDestruct (big_sepM2_dom with "Hgaddrm") as %Hdomeq.
      destruct ok; last first.
      { exfalso.
        apply map_get_false in Hok as [Hnotin _].
        by rewrite -not_elem_of_dom Hdomeq Hgids in Hnotin.
      }
      apply map_get_true in Hok.
      assert (is_Some (gaddrm !! gid)) as [addrm Haddrm].
      { by rewrite -elem_of_dom -Hdomeq elem_of_dom. }
      rewrite (drop_S _ _ _ Hgid) list_to_set_cons big_sepS_insert; last first.
      { rewrite not_elem_of_list_to_set. intros Hgidin.
        clear -Hgid Hgidin Hnd.
        rewrite -(take_drop_middle _ _ _ Hgid) in Hnd.
        apply NoDup_app in Hnd as (_ & _ & Hnd).
        by apply NoDup_cons in Hnd as [? _].
      }
      iDestruct "Htks" as "[Htk Htks]".
      wp_apply (wp_startBackupGroupCoordinator with "[] [$Hinv] [] Htk").
      { apply Hrk. }
      { apply Hin. }
      { specialize (Hrids _ _ Haddrm). apply Hrids. }
      { iApply (big_sepM2_lookup with "Hgaddrm").
        { apply Hok. }
        { apply Haddrm. }
      }
      { iApply (big_sepM_lookup with "Hinvnets"); first apply Haddrm. }
      iIntros (gcoord) "Hgcoord".
      wp_apply (wp_MapInsert with "HgcoordsP"); first done.
      iIntros "HgcoordsP".
      iApply "HΦ".
      iFrame "HgcoordsP".
      iSplitL "Hgcoords Hgcoord".
      { iApply (big_sepM_insert_2 with "[Hgcoord] Hgcoords").
        by iFrame "Hgcoord".
      }
      rewrite uint_nat_word_add_S; last word.
      iFrame "Htks".
      iPureIntro.
      rewrite dom_insert_L.
      rewrite (take_S_r _ _ _ Hgid) list_to_set_app_L Hdomgc /=.
      clear.
      set_solver.
    }
    iIntros "[HP _]".
    iNamed "HP".
    rewrite -Hlenptgs firstn_all HptgsL in Hdomgc.

    (*@     tcoord := &BackupTxnCoordinator{                                    @*)
    (*@         ts      : ts,                                                   @*)
    (*@         rank    : rank,                                                 @*)
    (*@         ptgs    : ptgs,                                                 @*)
    (*@         gcoords : gcoords,                                              @*)
    (*@         proph   : proph,                                                @*)
    (*@     }                                                                   @*)
    (*@     return tcoord                                                       @*)
    (*@ }                                                                       @*)
    wp_apply (wp_allocStruct).
    { by auto 10. }
    iIntros (gcoord) "Hgcoord".
    iDestruct (struct_fields_split with "Hgcoord") as "Hgcoord".
    iNamed "Hgcoord".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
