From Perennial.program_proof.tulip.program Require Import prelude.

Inductive rpres :=
| ReplicaOK
| ReplicaCommittedTxn
| ReplicaAbortedTxn
| ReplicaStaleCoordinator
| ReplicaFailedValidation
| ReplicaInvalidRank
| ReplicaWrongLeader.

Definition rpres_to_u64 (r : rpres) :=
  match r with
  | ReplicaOK => (U64 0)
  | ReplicaCommittedTxn => (U64 1)
  | ReplicaAbortedTxn => (U64 2)
  | ReplicaStaleCoordinator => (U64 3)
  | ReplicaFailedValidation => (U64 4)
  | ReplicaInvalidRank => (U64 5)
  | ReplicaWrongLeader => (U64 6)
  end.

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
      "Hprepm"   ∷ ([∗ map] s; m ∈ prepmS; prepm, ∃ l, own_dbmap_in_slice s l m) ∗
      "%Hcpmabs" ∷ ⌜(kmap Z.of_nat cpm : gmap Z dbmap) = kmap uint.Z prepm⌝.

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

  Definition ppsl_to_nat_bool (psl : ppsl) := (uint.nat psl.1, psl.2).

  Definition own_replica_psm_rkm
    (rp : loc) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat) : iProp Σ :=
    ∃ (pstblP : loc) (rktblP : loc) (pstbl : gmap u64 ppsl) (rktbl : gmap u64 u64),
      "HpstblP"  ∷ rp ↦[Replica :: "pstbl"] #pstblP ∗
      "HrktblP"  ∷ rp ↦[Replica :: "rktbl"] #rktblP ∗
      "Hpstbl"   ∷ own_map pstblP (DfracOwn 1) pstbl ∗
      "Hrktbl"   ∷ own_map rktblP (DfracOwn 1) rktbl ∗
      "%Hpsmabs" ∷ ⌜(kmap Z.of_nat psm : gmap Z (nat * bool)) = kmap uint.Z (fmap ppsl_to_nat_bool pstbl)⌝ ∗
      "%Hrkmabs" ∷ ⌜(kmap Z.of_nat rkm : gmap Z nat) = kmap uint.Z (fmap (λ x, uint.nat x) rktbl)⌝.

End repr.
