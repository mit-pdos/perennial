From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.tuple Require Import res.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.program.index Require Import index.
From Perennial.program_proof.tulip.paxos Require Import prelude.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Replica struct {                                                   @*)
  (*@     // Mutex.                                                           @*)
  (*@     mu *sync.Mutex                                                      @*)
  (*@     // Replica ID.                                                      @*)
  (*@     rid uint64                                                          @*)
  (*@     // Replicated transaction log.                                      @*)
  (*@     txnlog *txnlog.TxnLog                                               @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are application states.                             @*)
  (*@     //                                                                  @*)
  (*@     // LSN up to which all commands have been applied.                  @*)
  (*@     lsna   uint64                                                       @*)
  (*@     // Write sets of validated transactions.                            @*)
  (*@     prepm  map[uint64][]tulip.WriteEntry                                @*)
  (*@     // Participant groups of validated transactions.                    @*)
  (*@     ptgsm  map[uint64][]uint64                                          @*)
  (*@     // Prepare status table.                                            @*)
  (*@     pstbl  map[uint64]PrepareStatusEntry                                @*)
  (*@     // Transaction status table; mapping from transaction timestamps to their @*)
  (*@     // commit/abort status.                                             @*)
  (*@     txntbl map[uint64]bool                                              @*)
  (*@     // Mapping from keys to their prepare timestamps.                   @*)
  (*@     ptsm  map[string]uint64                                             @*)
  (*@     // Mapping from keys to their smallest preparable timestamps.       @*)
  (*@     sptsm map[string]uint64                                             @*)
  (*@     // Index.                                                           @*)
  (*@     idx    *index.Index                                                 @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are group info initialized after creation of all replicas. @*)
  (*@     //                                                                  @*)
  (*@     // Replicas in the same group. Read-only.                           @*)
  (*@     rps    map[uint64]grove_ffi.Address                                 @*)
  (*@     // ID of the replica believed to be the leader of this group. Used to @*)
  (*@     // initialize backup coordinators.                                  @*)
  (*@     leader uint64                                                       @*)
  (*@ }                                                                       @*)
  Definition own_replica_cm (rp : loc) (cm : gmap nat bool) : iProp Σ :=
    ∃ (txntblP : loc) (txntbl : gmap u64 bool),
      "HtxntblP" ∷ rp ↦[Replica :: "txntbl"] #txntblP ∗
      "Htxntbl"  ∷ own_map txntblP (DfracOwn 1) txntbl ∗
      "%Hcmabs"  ∷ ⌜(kmap Z.of_nat cm : gmap Z bool) = kmap uint.Z txntbl⌝.

  Definition own_replica_cpm (rp : loc) (cpm : gmap nat dbmap) : iProp Σ :=
    ∃ (prepmP : loc) (prepmS : gmap u64 Slice.t) (prepm : gmap u64 dbmap),
      "HprepmP"  ∷ rp ↦[Replica :: "prepm"] #prepmP ∗
      "HprepmS"  ∷ own_map prepmP (DfracOwn 1) prepmS ∗
      "#Hprepm"  ∷ ([∗ map] s; m ∈ prepmS; prepm, is_dbmap_in_slice s m) ∗
      "%Hcpmabs" ∷ ⌜(kmap Z.of_nat cpm : gmap Z dbmap) = kmap uint.Z prepm⌝.

  Definition own_replica_pgm (rp : loc) (pgm : gmap nat txnptgs) : iProp Σ :=
    ∃ (ptgsmP : loc) (ptgsmS : gmap u64 Slice.t) (ptgsm : gmap u64 txnptgs),
      "HptgsmP"  ∷ rp ↦[Replica :: "ptgsm"] #ptgsmP ∗
      "HptgsmS"  ∷ own_map ptgsmP (DfracOwn 1) ptgsmS ∗
      "#Hptgsm"  ∷ ([∗ map] s; g ∈ ptgsmS; ptgsm, is_txnptgs_in_slice s g) ∗
      "%Hpgmabs" ∷ ⌜(kmap Z.of_nat pgm : gmap Z txnptgs) = kmap uint.Z ptgsm⌝.

  Definition absrel_ptsm (ptsm : gmap dbkey nat) (ptsmM : gmap dbkey u64) :=
    ∀ k,
    k ∈ keys_all ->
    match ptsmM !! k with
    | Some ptsW => ptsm !! k = Some (uint.nat ptsW)
    | _ => ptsm !! k = Some O
    end.

  Definition own_replica_ptsm_sptsm
    (rp : loc) (ptsm sptsm : gmap dbkey nat) : iProp Σ :=
    ∃ (ptsmP : loc) (sptsmP : loc) (ptsmM : gmap dbkey u64) (sptsmM : gmap dbkey u64),
      "HptsmP"     ∷ rp ↦[Replica :: "ptsm"] #ptsmP ∗
      "HsptsmP"    ∷ rp ↦[Replica :: "sptsm"] #sptsmP ∗
      "HptsmM"     ∷ own_map ptsmP (DfracOwn 1) ptsmM ∗
      "HsptsmM"    ∷ own_map sptsmP (DfracOwn 1) sptsmM ∗
      "%Hptsmabs"  ∷ ⌜absrel_ptsm ptsm ptsmM⌝ ∗
      "%Hsptsmabs" ∷ ⌜absrel_ptsm sptsm sptsmM⌝.

  Lemma own_replica_ptsm_sptsm_dom rp ptsm sptsm :
    own_replica_ptsm_sptsm rp ptsm sptsm -∗
    ⌜keys_all ⊆ dom ptsm ∧ keys_all ⊆ dom sptsm⌝.
  Proof.
    iNamed 1.
    iPureIntro.
    split.
    - intros k Hk. specialize (Hptsmabs _ Hk).
      apply elem_of_dom. by destruct (ptsmM !! k).
    - intros k Hk. specialize (Hsptsmabs _ Hk).
      apply elem_of_dom. by destruct (sptsmM !! k).
  Qed.

  Definition own_replica_psm_rkm
    (rp : loc) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat) : iProp Σ :=
    ∃ (pstblP : loc) (rktblP : loc) (pstbl : gmap u64 ppsl) (rktbl : gmap u64 u64),
      "HpstblP"  ∷ rp ↦[Replica :: "pstbl"] #pstblP ∗
      "HrktblP"  ∷ rp ↦[Replica :: "rktbl"] #rktblP ∗
      "Hpstbl"   ∷ own_map pstblP (DfracOwn 1) pstbl ∗
      "Hrktbl"   ∷ own_map rktblP (DfracOwn 1) rktbl ∗
      "%Hvrank"  ∷ ⌜map_Forall (λ _ rk, (0 < rk)%nat) rkm⌝ ∗
      "%Hpsmabs" ∷ ⌜(kmap Z.of_nat psm : gmap Z (nat * bool)) = kmap uint.Z (fmap ppsl_to_nat_bool pstbl)⌝ ∗
      "%Hrkmabs" ∷ ⌜(kmap Z.of_nat rkm : gmap Z nat) = kmap uint.Z (fmap (λ x, uint.nat x) rktbl)⌝.

  Definition own_replica_histm (rp : loc) (histm : gmap dbkey dbhist) α : iProp Σ :=
    ([∗ map] k ↦ h ∈ histm, own_phys_hist_half α k h).

  Definition is_replica_fname (rp : loc) (gid rid : u64) γ : iProp Σ :=
    ∃ (fname : byte_string),
      "HfnameP" ∷ readonly (rp ↦[Replica :: "fname"] #(LitString fname)) ∗
      "#Hfname" ∷ is_replica_ilog_fname γ gid rid fname.

  Definition own_replica_with_cloga_no_lsna
    (rp : loc) (cloga : dblog) (gid rid : u64) γ α : iProp Σ :=
    ∃ (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (pgm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat)
      (clog : dblog) (ilog : list (nat * icommand)),
      let log := merge_clog_ilog cloga ilog in
      let dst := ReplicaDurable clog ilog in
      "Hcm"         ∷ own_replica_cm rp cm ∗
      "Hhistm"      ∷ own_replica_histm rp histm α ∗
      "Hcpm"        ∷ own_replica_cpm rp cpm ∗
      "Hpgm"        ∷ own_replica_pgm rp pgm ∗
      "Hptsmsptsm"  ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "Hpsmrkm"     ∷ own_replica_psm_rkm rp psm rkm ∗
      "Hdurable"    ∷ own_crash_ex rpcrashNS (own_replica_durable γ gid rid) dst ∗
      "#Hfname"     ∷ is_replica_fname rp gid rid γ ∗
      "#Hrpvds"     ∷ ([∗ set] t ∈ dom cpm, is_replica_validated_ts γ gid rid t) ∗
      "#Hsafetpwrs" ∷ ([∗ map] t ↦ pwrs ∈ cpm, safe_txn_pwrs γ gid t pwrs) ∗
      "#Hfpw"       ∷ ([∗ map] t ↦ ps ∈ psm, fast_proposal_witness γ gid rid t ps) ∗
      "#Hlnrzs"     ∷ ([∗ set] t ∈ dom pgm, is_lnrz_tid γ t) ∗
      "#Hsafebk"    ∷ ([∗ map] t ↦ g ∈ pgm, safe_backup_txn γ t g) ∗
      "#Hclogalb"   ∷ is_txn_log_lb γ gid cloga ∗
      "%Hdompsmrkm" ∷ ⌜dom psm = dom rkm⌝ ∗
      "%Hcloga"     ∷ ⌜prefix clog cloga⌝ ∗
      "%Hvcpm"      ∷ ⌜map_Forall (λ _ m, valid_wrs m) cpm⌝ ∗
      "%Hvicmds"    ∷ ⌜Forall (λ nc, (nc.1 <= length cloga)%nat) ilog⌝ ∗
      "%Hexec"      ∷ ⌜execute_cmds log = LocalState cm histm cpm pgm sptsm ptsm psm rkm⌝.

  Definition own_replica_lsna (rp : loc) (lsna : nat) : iProp Σ :=
    ∃ (lsnaW : u64),
      "HlsnaP"  ∷ rp ↦[Replica :: "lsna"] #lsnaW ∗
      "%HlsnaW" ∷ ⌜uint.nat lsnaW = lsna⌝.

  Definition own_replica (rp : loc) (gid rid : u64) γ α : iProp Σ :=
    ∃ (cloga : dblog) (lsna : nat),
      "Hrp"        ∷ own_replica_with_cloga_no_lsna rp cloga gid rid γ α ∗
      "Hlsna"      ∷ own_replica_lsna rp lsna ∗
      "%Hlencloga" ∷ ⌜length cloga = lsna⌝.

  Definition own_replica_replaying
    (rp : loc) (clog : dblog) (ilog : list (nat * icommand)) α : iProp Σ :=
    ∃ (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (pgm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat),
      let log := merge_clog_ilog clog ilog in
      "Hcm"        ∷ own_replica_cm rp cm ∗
      "Hhistm"     ∷ own_replica_histm rp histm α ∗
      "Hcpm"       ∷ own_replica_cpm rp cpm ∗
      "Hpgm"       ∷ own_replica_pgm rp pgm ∗
      "Hptsmsptsm" ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "Hpsmrkm"    ∷ own_replica_psm_rkm rp psm rkm ∗
      "%Hvcpm"     ∷ ⌜map_Forall (λ _ m, valid_wrs m) cpm⌝ ∗
      "%Hexec"     ∷ ⌜execute_cmds log = LocalState cm histm cpm pgm sptsm ptsm psm rkm⌝.

  Definition own_replica_replaying_in_lsn
    (rp : loc) (lsna : nat) (ilog : list (nat * icommand)) gid γ α : iProp Σ :=
    ∃ (clog : dblog),
      "Hrp"       ∷ own_replica_replaying rp clog ilog α ∗
      "#Hcloglb"  ∷ is_txn_log_lb γ gid clog ∗
      "%Hlenclog" ∷ ⌜length clog = lsna⌝.
  
  Definition is_replica_idx (rp : loc) γ α : iProp Σ :=
    ∃ (idx : loc),
      "#HidxP" ∷ readonly (rp ↦[Replica :: "idx"] #idx) ∗
      "#Hidx"  ∷ is_index idx γ α.

  Definition is_replica_gid_rid (rp : loc) (gid rid : u64) : iProp Σ :=
    "#HgidP" ∷ readonly (rp ↦[Replica :: "gid"] #gid) ∗
    "#HridP" ∷ readonly (rp ↦[Replica :: "rid"] #rid) ∗
    "%Hgid"  ∷ ⌜gid ∈ gids_all⌝ ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition is_replica_proph (rp : loc) (proph : proph_id) : iProp Σ :=
    "#HprophP" ∷ readonly (rp ↦[Replica :: "proph"] #proph).

  Definition is_replica_gaddrm (rp : loc) γ : iProp Σ :=
    ∃ (gaddrmPP : loc) (gaddrmP : gmap u64 loc) (gaddrm : gmap u64 (gmap u64 chan)),
      "#HgaddrmPP"  ∷ readonly (rp ↦[Replica :: "gaddrm"] #gaddrmPP) ∗
      "#HgaddrmP"   ∷ own_map gaddrmPP DfracDiscarded gaddrmP ∗
      "#Hgaddrm"    ∷ ([∗ map] addrmP; addrm ∈ gaddrmP; gaddrm, own_map addrmP DfracDiscarded addrm) ∗
      "#Hinvnets"   ∷ ([∗ map] gid ↦ addrm ∈ gaddrm, know_tulip_network_inv γ gid addrm) ∗
      "%Hdomgaddrm" ∷ ⌜dom gaddrm = gids_all⌝ ∗
      "%Hdomaddrm"  ∷ ⌜map_Forall (λ _ addrm, dom addrm = rids_all) gaddrm⌝.

  (* TODO: rename this to [is_replica_core] and the one below to just [is_replica]. *)
  Definition is_replica (rp : loc) (gid rid : u64) γ : iProp Σ :=
    ∃ (mu : loc) (proph : proph_id) α,
      "#HmuP"     ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"    ∷ is_lock tulipNS #mu (own_replica rp gid rid γ α) ∗
      "#Hidx"     ∷ is_replica_idx rp γ α ∗
      "#Hgidrid"  ∷ is_replica_gid_rid rp gid rid ∗
      "#Hgaddrm"  ∷ is_replica_gaddrm rp γ ∗
      "#Hproph"   ∷ is_replica_proph rp proph ∗
      "#Hinv"     ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hinvfile" ∷ know_replica_file_inv γ gid rid.

End repr.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Definition is_replica_txnlog (rp : loc) gid γ : iProp Σ :=
    ∃ (txnlog : loc),
      "#HtxnlogP" ∷ readonly (rp ↦[Replica :: "txnlog"] #txnlog) ∗
      "#Htxnlog"  ∷ is_txnlog txnlog gid γ.

  Definition is_replica_plus_txnlog (rp : loc) gid rid γ : iProp Σ :=
    "#Hrp"     ∷ is_replica rp gid rid γ ∗
    "#Htxnlog" ∷ is_replica_txnlog rp gid γ.

  Definition is_replica_plus_network (rp : loc) (addr : chan) (gid rid : u64) γ : iProp Σ :=
    ∃ (addrm : gmap u64 chan),
      "#HaddrP"  ∷ readonly (rp ↦[Replica :: "addr"] (to_val addr)) ∗
      "#Hinvnet" ∷ know_tulip_network_inv γ gid addrm ∗
      "Hrp"      ∷ is_replica_plus_txnlog rp gid rid γ ∗
      "%Haddr"   ∷ ⌜addrm !! rid = Some addr⌝.

End repr.
