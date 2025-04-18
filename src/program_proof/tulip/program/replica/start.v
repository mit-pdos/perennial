From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_resume.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.program.tuple Require Import res.
From Perennial.program_proof.tulip.program.index Require Import index.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_serve replica_applier replica_backup.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import replica.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_start
    (gid rid : u64) (addr : chan) (fname : byte_string) (proph : proph_id)
    (addrmpxP : loc) (fnamepx : byte_string)
    (termc : u64) (terml : u64) (lsnc : u64) (logpx : list byte_string) (addrmpx : gmap u64 chan)
    (clog : dblog) (ilog : list (nat * icommand)) (addrm : gmap u64 chan)
    (gaddrmPP : loc) (gaddrmP : gmap u64 loc) (gaddrm : gmap u64 (gmap u64 chan)) γ π :
    let dstpx := PaxosDurable termc terml logpx lsnc in
    let dstrp := ReplicaDurable clog ilog in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    addrm !! rid = Some addr ->
    dom gaddrm = gids_all ->
    map_Forall (λ _ addrm, dom addrm = rids_all) gaddrm ->
    is_node_wal_fname π rid fnamepx -∗
    is_replica_ilog_fname γ gid rid fname -∗
    (* paxos atomic invariants *)
    know_paxos_inv π (dom addrmpx) -∗
    know_paxos_file_inv π (dom addrmpx) -∗
    know_paxos_network_inv π addrmpx -∗
    (* txnlog atomic invariants *)
    know_tulip_txnlog_inv γ π gid -∗
    (* tulip atomic invariants *)
    know_tulip_inv_with_proph γ proph -∗
    know_replica_file_inv γ gid rid -∗
    know_tulip_network_inv γ gid addrm -∗
    (* backup coordinator *)
    own_map gaddrmPP DfracDiscarded gaddrmP -∗
    ([∗ map] addrmP; addrm ∈ gaddrmP; gaddrm, own_map addrmP DfracDiscarded addrm) -∗
    ([∗ map] gid ↦ addrm ∈ gaddrm, know_tulip_network_inv γ gid addrm) -∗
    {{{ (* durable states passed to paxos *)
        own_map addrmpxP (DfracOwn 1) addrmpx ∗
        own_crash_ex pxcrashNS (own_paxos_durable π rid) dstpx ∗
        own_crash_ex (stagedG0 := tulip_ghostG0.(@tulip_stagedG Σ))
          rpcrashNS (own_replica_durable γ gid rid) dstrp
    }}}
      start #gid #rid (to_val addr) #(LitString fname) #addrmpxP #(LitString fnamepx) #gaddrmPP #proph
    {{{ (rp : loc), RET #rp; is_replica rp gid rid γ }}}.
  Proof.
    iIntros (dstpx dstrp Hgid Hrid Hdomgaddrm Hdomaddrm Haddr).
    iIntros "#Hfnamewal #Hfnameilog #Hinvpx #Hinvpxfile #Hinvpxnet".
    iIntros "#Hinvtxnlog #Hinv #Hinvfile #Hinvnet".
    iIntros "#HgaddrmP #Hgaddrm #Hinvnets".
    iIntros (Φ).
    iIntros "!> (Haddrmpx & Hdurablepx & Hdurable) HΦ".
    wp_rec. wp_pures.

    (*@ func Start(rid uint64, addr grove_ffi.Address, fname string, addrmpx map[uint64]uint64, fnamepx string) *Replica { @*)
    (*@     txnlog := txnlog.Start(rid, addrmpx, fnamepx)                       @*)
    (*@                                                                         @*)
    wp_apply (wp_Start
      with "Hfnamewal Hinvpx Hinvpxfile Hinvpxnet Hinvtxnlog [$Haddrmpx $Hdurablepx]").
    iIntros (txnlogP) "#Htxnlog".

    (*@     rp := &Replica{                                                     @*)
    (*@         mu     : new(sync.Mutex),                                       @*)
    (*@         rid    : rid,                                                   @*)
    (*@         addr   : addr,                                                  @*)
    (*@         fname  : fname,                                                 @*)
    (*@         txnlog : txnlog,                                                @*)
    (*@         lsna   : 0,                                                     @*)
    (*@         prepm  : make(map[uint64][]tulip.WriteEntry),                   @*)
    (*@         ptgsm  : make(map[uint64][]uint64),                             @*)
    (*@         pstbl  : make(map[uint64]PrepareProposal),                      @*)
    (*@         rktbl  : make(map[uint64]uint64),                               @*)
    (*@         txntbl : make(map[uint64]bool),                                 @*)
    (*@         ptsm   : make(map[string]uint64),                               @*)
    (*@         sptsm  : make(map[string]uint64),                               @*)
    (*@         idx    : index.MkIndex(),                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_NewMap u64 Slice.t).
    iIntros (prepmP) "Hprepm".
    wp_apply (wp_NewMap u64 Slice.t).
    iIntros (ptgsmP) "Hptgsm".
    wp_apply wp_NewMap.
    iIntros (pstblP) "Hpstbl".
    wp_apply wp_NewMap.
    iIntros (rktblP) "Hrktbl".
    wp_apply wp_NewMap.
    iIntros (txntblP) "Htxntbl".
    wp_apply wp_NewMap.
    iIntros (ptsmP) "Hptsm".
    wp_apply wp_NewMap.
    iIntros (sptsmP) "Hsptsm".
    (* Allocate physical history. *)
    iMod phys_hist_alloc as (α) "[Hphysm HphysmX]".
    (* Obtain lower bounds of txn log and replicated history for later use. *)
    iAssert (|={⊤}=> is_txn_log_lb γ gid [])%I as "Htxnloglb".
    { iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
      { apply Hgid. }
      iDestruct (group_inv_extract_log with "Hgroup") as (tlog) "[Htlog Hgroup]".
      iDestruct (txn_log_witness with "Htlog") as "#Htloglb".
      iDestruct (txn_log_lb_weaken [] with "Htloglb") as "#Htloglb'".
      { apply prefix_nil. }
      iDestruct (group_inv_merge_log with "Htlog Hgroup") as "Hgroup".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    }
    iMod "Htxnloglb" as "#Htxnloglb".
    iAssert (|={⊤}=> [∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None])%I as "Hrepllb".
    { iNamed "Hinv".
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iAssert ([∗ set] key ∈ keys_all, is_repl_hist_lb γ key [None])%I as "#Hreplm".
      { iApply (big_sepS_mono with "Hkeys").
        iIntros (k Hk) "Hkey".
        do 2 iNamed "Hkey".
        iDestruct (repl_hist_witness with "Hrepl") as "#Hrepllb".
        iDestruct (repl_hist_lb_weaken [None] with "Hrepllb") as "#Hrepllb'".
        { by apply prefix_singleton. }
        done.
      }
      by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    }
    iMod "Hrepllb" as "#Hrepllb".
    wp_apply (wp_MkIndex with "Hrepllb HphysmX").
    iIntros (idxP) "#Hidx".
    wp_apply (wp_allocStruct).
    { by auto 25. }
    iIntros (rp) "Hrp".
    iDestruct (struct_fields_split with "Hrp") as "Hrp".
    iNamed "Hrp".
    (* Make read-only persistent resources. *)
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iMod (readonly_alloc_1 with "addr") as "#HaddrP".
    iMod (readonly_alloc_1 with "gid") as "#HgidP".
    iMod (readonly_alloc_1 with "rid") as "#HridP".
    iMod (readonly_alloc_1 with "idx") as "#HidxP".
    iMod (readonly_alloc_1 with "txnlog") as "#HtxnlogP".
    iMod (readonly_alloc_1 with "fname") as "#HfnameP".
    iMod (readonly_alloc_1 with "gaddrm") as "#HgaddrmPP".
    iMod (readonly_alloc_1 with "proph") as "#HprophP".
    iAssert (own_replica_cm rp ∅)%I with "[$txntbl $Htxntbl]" as "Hcm"; first done.
    iAssert (own_replica_histm rp (gset_to_gmap [None] keys_all : gmap dbkey dbhist) α)%I
      with "[Hphysm]" as "Hhistm".
    { iApply (big_sepS_sepM_impl with "Hphysm").
      { by rewrite dom_gset_to_gmap. }
      iIntros (k h Hh) "!> Hphys".
      by apply lookup_gset_to_gmap_Some in Hh as [_ <-].
    }
    iAssert (own_replica_cpm rp ∅)%I with "[$prepm $Hprepm]" as "Hcpm".
    { iExists ∅. by rewrite big_sepM2_empty. }
    iAssert (own_replica_pgm rp ∅)%I with "[$ptgsm $Hptgsm]" as "Hpgm".
    { iExists ∅. by rewrite big_sepM2_empty. }
    set ptsm_init : gmap dbkey nat := gset_to_gmap O keys_all.
    iAssert (own_replica_ptsm_sptsm rp ptsm_init ptsm_init)%I
      with "[$ptsm $sptsm $Hptsm $Hsptsm]" as "Hptsmsptsm".
    { iPureIntro.
      split.
      { intros k Hk. by rewrite lookup_empty lookup_gset_to_gmap_Some. }
      { intros k Hk. by rewrite lookup_empty lookup_gset_to_gmap_Some. }
    }
    iAssert (own_replica_psm_rkm rp ∅ ∅)%I
      with "[$pstbl $rktbl $Hpstbl $Hrktbl]" as "Hpsmrkm"; first done.
    iAssert (own_replica_lsna rp O)%I with "[$lsna]" as "Hlsna"; first done.
    iAssert (is_replica_fname rp gid rid γ)%I with "[$HfnameP $Hfnameilog]" as "Hfname".
    iAssert (own_replica_replaying rp [] [] α)%I with
      "[$Hcm $Hhistm $Hcpm $Hpgm $Hptsmsptsm $Hpsmrkm]" as "Hrp".
    { iPureIntro. by rewrite merge_clog_ilog_nil. }
    iAssert (is_replica_idx rp γ α)%I with "[$HidxP $Hidx]" as "#Hidxrp".
    iAssert (is_replica_gid_rid rp gid rid)%I with "[$HgidP $HridP]" as "#Hgidrid".
    { done. }
    iAssert (is_replica_gaddrm rp γ)%I as "#Hgaddrmrp".
    { by iFrame "# %". }
    iAssert (is_replica_proph rp proph)%I with "[$HprophP]" as "#Hproph".
    iAssert (is_replica_txnlog rp gid γ)%I with "[$HtxnlogP $Htxnlog]" as "Htxnlogrp".
    wp_apply (wp_Replica__resume with
               "[$Hinv] Hinvfile Hfname Hidxrp Htxnlogrp [$Hrp $Hlsna $Hdurable]").
    { apply Hgid. }
    { apply Hrid. }
    iIntros "(Hrp & Hlsna & Hdurable)".
    iAssert (|NC={⊤}=> own_replica rp gid rid γ α)%I with "[Hrp Hlsna Hdurable]" as "> Hrp".
    { iNamed "Hrp".
      (* Open the crash and atomic replica invariants. *)
      iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
      { solve_ndisj. }
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
      { apply Hgid. }
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]".
      { apply Hrid. }
      do 2 iNamed "Hrp".
      iNamedSuffix "Hdurable" "X".
      (* Prove equality between logs and applications states. *)
      iDestruct (replica_clog_agree with "HclogX Hclog") as %->.
      iDestruct (replica_ilog_agree with "HilogX Hilog") as %->.
      rewrite Hrsm in Hexec. inv Hexec.
      (* Close the crash and atomic replica invariants. *)
      iDestruct ("HrgC" with "[$Hvtss $Hclog $Hilog $Hkvdm $Hbm $Hbackup]") as "Hrg".
      { by iFrame "# %". }
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iMod ("HdurableC" $! dstrp with "[$HclogX $HilogX]") as "Hdurable".
      iModIntro.
      iFrame "Hlsna".
      iExists clog.
      iSplit; last done.
      iFrame "∗ # %".
      iPureIntro.
      split; last done.
      pose proof (map_Forall2_dom_L _ _ _ Hbmpsm) as <-.
      by pose proof (map_Forall2_dom_L _ _ _ Hbmrkm) as <-.
    }
    iMod (alloc_lock _ _ _ (own_replica rp gid rid γ α) with "Hfree [$Hrp]") as "#Hlock".
    iAssert (is_replica rp gid rid γ)%I as "#Hrp".
    { by iFrame "#". }
    iAssert (is_replica_plus_txnlog rp gid rid γ)%I as "#Hrptxnlog".
    { by iFrame "#". }
    iAssert (is_replica_plus_network rp addr gid rid γ)%I as "#Hrpnet".
    { by iFrame "#". }
    wp_pures.

    (*@     go func() {                                                         @*)
    (*@         rp.Serve()                                                      @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Replica__Serve with "Hrpnet"). }

    (*@     go func() {                                                         @*)
    (*@         rp.Applier()                                                    @*)
    (*@     }()                                                                 @*)
    (*@                                                                         @*)
    wp_apply wp_fork.
    { by wp_apply (wp_Replica__Applier with "Hrptxnlog"). }
    wp_pures.

    wp_apply wp_fork.
    { by wp_apply (wp_Replica__Backup with "Hrp"). }
    wp_pures.

    (*@     return rp                                                           @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
