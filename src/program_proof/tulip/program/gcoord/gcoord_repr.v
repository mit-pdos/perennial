From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  greader_repr gpreparer_repr.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type GroupCoordinator struct {                                          @*)
  (*@     // Replica addresses. Read-only.                                    @*)
  (*@     rps     map[uint64]grove_ffi.Address                                @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu      *sync.Mutex                                                 @*)
  (*@     // Condition variable used to notify arrival of responses.          @*)
  (*@     cv      *sync.Cond                                                  @*)
  (*@     // Timestamp of the currently active transaction.                   @*)
  (*@     ts       uint64                                                     @*)
  (*@     // ID of the replica believed to be the leader of this group.       @*)
  (*@     leader   uint64                                                     @*)
  (*@     // Group reader.                                                    @*)
  (*@     grd      *GroupReader                                               @*)
  (*@     // Group preparer.                                                  @*)
  (*@     gpp      *GroupPreparer                                             @*)
  (*@     // IDs of the finalizing transactions. Using unit as range would suffice. @*)
  (*@     tsfinals map[uint64]bool                                            @*)
  (*@     // Connections to replicas.                                         @*)
  (*@     conns    map[uint64]grove_ffi.Connection                            @*)
  (*@ }                                                                       @*)
  Definition own_gcoord_ts gcoord ts : iProp Σ :=
    ∃ (tsW : u64),
      "HtsW" ∷ gcoord ↦[GroupCoordinator :: "ts"] #tsW ∗
      "%Hts" ∷ ⌜uint.nat tsW = ts⌝.

  Definition own_gcoord_greader gcoord ts γ : iProp Σ :=
    ∃ (grdP : loc),
      "HgrdP" ∷ gcoord ↦[GroupCoordinator :: "grd"] #grdP ∗
      "Hgrd"  ∷ own_greader grdP ts γ.

  Definition own_gcoord_gpreparer gcoord ts gid γ : iProp Σ :=
    ∃ (gppP : loc),
      "HgppP" ∷ gcoord ↦[GroupCoordinator :: "gpp"] #gppP ∗
      "Hgpp"  ∷ own_gpreparer gppP ts gid γ.

  Definition own_gcoord_finalizer gcoord (rids : gset u64) : iProp Σ :=
    ∃ (idxleader : u64) (tsfinalsP : loc) (tsfinals : gmap u64 bool),
      "Hleader"    ∷ gcoord ↦[GroupCoordinator :: "idxleader"] #idxleader ∗
      "HtsfinalsP" ∷ gcoord ↦[GroupCoordinator :: "tsfinals"] #tsfinalsP ∗
      "Htsfinals"  ∷ own_map tsfinalsP (DfracOwn 1) tsfinals ∗
      "%Hleader"   ∷ ⌜(uint.nat idxleader < size rids)⌝.

  Definition own_gcoord_core gcoord ts gid rids γ : iProp Σ :=
    "Hts"  ∷ own_gcoord_ts gcoord ts ∗
    "Hgrd" ∷ own_gcoord_greader gcoord ts γ ∗
    "Hgpp" ∷ own_gcoord_gpreparer gcoord ts gid γ ∗
    "Hgfl" ∷ own_gcoord_finalizer gcoord rids.

  Definition own_gcoord_comm gcoord (addrm : gmap u64 chan) gid γ : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ gcoord ↦[GroupCoordinator :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ gid x.1) ∗
      "%Haddrm" ∷ ⌜map_Forall (λ rid x, addrm !! rid = Some x.2) conns⌝.

  Definition own_gcoord_with_ts gcoord addrm ts gid γ : iProp Σ :=
    "Hgcoord" ∷ own_gcoord_core gcoord ts gid (dom addrm) γ ∗
    "Hcomm"   ∷ own_gcoord_comm gcoord addrm gid γ.

  Definition own_gcoord gcoord addrm gid γ : iProp Σ :=
    ∃ ts, "Hgcoord" ∷ own_gcoord_with_ts gcoord addrm ts gid γ.

  Definition is_gcoord_addrm gcoord (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (addrmP : loc) (rpsP : Slice.t) (rps : list u64),
      "#HaddrmP"   ∷ readonly (gcoord ↦[GroupCoordinator :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm ∗
      "#HrpsP"     ∷ readonly (gcoord ↦[GroupCoordinator :: "rps"] (to_val rpsP)) ∗
      "#Hrps"      ∷ readonly (own_slice_small rpsP uint64T (DfracOwn 1) rps) ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = list_to_set rps⌝ ∗
      (* right now [rps] is redundant since the set of replicas are fixed up
      front, but keeping it makes it easier to remove this constraint *)
      "%Hrps"      ∷ ⌜list_to_set rps = rids_all⌝ ∗
      "%Hnodup"    ∷ ⌜NoDup rps⌝.

  Definition is_gcoord_with_addrm gcoord gid (addrm : gmap u64 chan) γ : iProp Σ :=
    ∃ (muP : loc) (cvP cvrsP : loc),
      "#HmuP"    ∷ readonly (gcoord ↦[GroupCoordinator :: "mu"] #muP) ∗
      "#Hlock"   ∷ is_lock tulipNS #muP (own_gcoord gcoord addrm gid γ) ∗
      "#HcvP"    ∷ readonly (gcoord ↦[GroupCoordinator :: "cv"] #cvP) ∗
      "#Hcv"     ∷ is_cond cvP #muP ∗
      "#HcvrsP"  ∷ readonly (gcoord ↦[GroupCoordinator :: "cvrs"] #cvrsP) ∗
      "#Hcvrs"   ∷ is_cond cvrsP #muP ∗
      "#Hinv"    ∷ know_tulip_inv γ ∗
      "#Hinvnet" ∷ know_tulip_network_inv γ gid addrm ∗
      "#Haddrm"  ∷ is_gcoord_addrm gcoord addrm ∗
      "%Hgid"    ∷ ⌜gid ∈ gids_all⌝.

  Definition is_gcoord gcoord gid γ : iProp Σ :=
    ∃ addrm, "Hgcoord" ∷ is_gcoord_with_addrm gcoord gid addrm γ.

End repr.
