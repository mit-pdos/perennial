From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type BackupGroupCoordinator struct {                                    @*)
  (*@     // Replica IDs in this group.                                       @*)
  (*@     rps       []uint64                                                  @*)
  (*@     // Replica addresses. Read-only.                                    @*)
  (*@     addrm     map[uint64]grove_ffi.Address                              @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu        *sync.Mutex                                               @*)
  (*@     // Condition variable used to notify arrival of responses.          @*)
  (*@     cv        *sync.Cond                                                @*)
  (*@     // The replica believed to be the leader of this group.             @*)
  (*@     idxleader uint64                                                    @*)
  (*@     // Group preparer.                                                  @*)
  (*@     gpp       *BackupGroupPreparer                                      @*)
  (*@     // Connections to replicas.                                         @*)
  (*@     conns     map[uint64]grove_ffi.Connection                           @*)
  (*@ }                                                                       @*)
  Definition own_backup_gcoord_gpreparer gcoord rk ts cid gid γ : iProp Σ :=
    ∃ (gppP : loc),
      "HgppP" ∷ gcoord ↦[BackupGroupCoordinator :: "gpp"] #gppP ∗
      "Hgpp"  ∷ own_backup_gpreparer gppP rk ts cid gid γ.

  Definition own_backup_gcoord_comm gcoord (addrm : gmap u64 chan) gid γ : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ gcoord ↦[BackupGroupCoordinator :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ gid x.1) ∗
      "%Haddrm" ∷ ⌜map_Forall (λ rid x, addrm !! rid = Some x.2) conns⌝.

  Definition own_backup_gcoord_leader gcoord (rids : gset u64) : iProp Σ :=
    ∃ (idxleader : u64),
      "Hleader"    ∷ gcoord ↦[BackupGroupCoordinator :: "idxleader"] #idxleader ∗
      "%Hleader"   ∷ ⌜(uint.nat idxleader < size rids)⌝.

  Definition own_backup_gcoord gcoord addrm rk ts cid gid γ : iProp Σ :=
    "Hgpp"    ∷ own_backup_gcoord_gpreparer gcoord rk ts cid gid γ ∗
    "Hcomm"   ∷ own_backup_gcoord_comm gcoord addrm gid γ ∗
    "Hleader" ∷ own_backup_gcoord_leader gcoord (dom addrm).

  Definition is_backup_gcoord_addrm gcoord (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (addrmP : loc) (rpsP : Slice.t) (rps : list u64),
      "#HaddrmP"   ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm ∗
      "#HrpsP"     ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "rps"] (to_val rpsP)) ∗
      "#Hrps"      ∷ readonly (own_slice_small rpsP uint64T (DfracOwn 1) rps) ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = list_to_set rps⌝ ∗
      (* right now [rps] is redundant since the set of replicas are fixed up
      front, but keeping it makes it easier to remove this constraint *)
      "%Hrps"      ∷ ⌜list_to_set rps = rids_all⌝ ∗
      "%Hnodup"    ∷ ⌜NoDup rps⌝.

  (* TODO: build a better abstraction similarly to [is_gcoord_with_addrm] *)
  Definition is_backup_gcoord_with_addrm gcoord (addrm : gmap u64 chan) rk ts gid γ : iProp Σ :=
    ∃ (muP : loc) (cvP : loc) (cid : coordid) (rankW tsW : u64),
      "#HmuP"    ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "mu"] #muP) ∗
      "#Hlock"   ∷ is_lock tulipNS #muP (own_backup_gcoord gcoord addrm rk ts cid gid γ) ∗
      "#HcvP"    ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "cv"] #cvP) ∗
      "#Hcv"     ∷ is_cond cvP #muP ∗
      "#HcidP"   ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "cid"] (coordid_to_val cid)) ∗
      "#HtsP"    ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "ts"] #tsW) ∗
      "#HrankP"  ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "rank"] #rankW) ∗
      "#Hinv"    ∷ know_tulip_inv γ ∗
      "#Hinvnet" ∷ know_tulip_network_inv γ gid addrm ∗
      "#Haddrm"  ∷ is_backup_gcoord_addrm gcoord addrm ∗
      "%Hgid"    ∷ ⌜gid ∈ gids_all⌝ ∗
      "%Hrk"     ∷ ⌜(1 < rk)%nat⌝ ∗
      "%HtsW"    ∷ ⌜ts = uint.nat tsW⌝ ∗
      "%rankW"   ∷ ⌜rk = uint.nat rankW⌝.

  Definition is_backup_gcoord gcoord rk ts gid γ : iProp Σ :=
    ∃ addrm, "Hgcoord" ∷ is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ.

End repr.
