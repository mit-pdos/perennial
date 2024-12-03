From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import read.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type GroupReader struct {                                               @*)
  (*@     // Number of replicas. Read-only.                                   @*)
  (*@     nrps   uint64                                                       @*)
  (*@     // Cached read set. Exists for performance reason; could have an interface @*)
  (*@     // to create a transaction that does not cache reads.               @*)
  (*@     valuem map[string]tulip.Value                                       @*)
  (*@     // Versions responded by each replica for each key. Instead of using a @*)
  (*@     // single map[uint64]Version for the current key being read, this design allows @*)
  (*@     // supporting more sophisticated "async-read" in future.            @*)
  (*@     qreadm map[string]map[uint64]tulip.Version                          @*)
  (*@ }                                                                       @*)
  Definition own_greader_valuem
    (grd : loc) (valuem : gmap dbkey dbval) (ts : nat) γ : iProp Σ :=
    ∃ (valuemP : loc),
      "HvaluemP" ∷ grd ↦[GroupReader :: "valuem"] #valuemP ∗
      "Hvaluem"  ∷ own_map valuemP (DfracOwn 1) valuem ∗
      "#Hfinal"  ∷ ([∗ map] k ↦ v ∈ valuem, fast_or_quorum_read γ k ts v).

  Definition own_greader_qreadm
    (grd : loc) (qreadm : gmap dbkey (gmap u64 (u64 * dbval))) (ts : nat) γ : iProp Σ :=
    ∃ (qreadmP : loc) (qreadmM : gmap dbkey loc) ,
      "HqreadmP" ∷ grd ↦[GroupReader :: "qreadm"] #qreadmP ∗
      "HqreadmM" ∷ own_map qreadmP (DfracOwn 1) qreadmM ∗
      "Hqreadm"  ∷ ([∗ map] k ↦ p; m ∈ qreadmM; qreadm, own_map p (DfracOwn 1) m) ∗
      "#Hqread"  ∷ ([∗ map] k ↦ m ∈ qreadm,
                      [∗ map] rid ↦ ver ∈ m, slow_read γ rid k (uint.nat ver.1) ts ver.2) ∗
      "%Hvrids"  ∷ ⌜map_Forall (λ _ m, dom m ⊆ rids_all) qreadm⌝.

  Definition own_greader_nrps (grd : loc) : iProp Σ :=
    ∃ (nrps : u64),
      "Hnrps"   ∷ grd ↦[GroupReader :: "nrps"] #nrps ∗
      "%Hnrps"  ∷ ⌜uint.nat nrps = size rids_all⌝.

  Definition own_greader (grd : loc) (ts : nat) γ : iProp Σ :=
    ∃ (valuem : gmap dbkey dbval) (qreadm : gmap dbkey (gmap u64 (u64 * dbval))),
      "Hvaluem" ∷ own_greader_valuem grd valuem ts γ ∗
      "Hqreadm" ∷ own_greader_qreadm grd qreadm ts γ ∗
      "Hnrps"   ∷ own_greader_nrps grd.

  Definition own_greader_uninit (grd : loc) : iProp Σ :=
    ∃ (valuemP qreadmP : loc),
      "HvaluemP" ∷ grd ↦[GroupReader :: "valuem"] #valuemP ∗
      "HqreadmP" ∷ grd ↦[GroupReader :: "qreadm"] #qreadmP ∗
      "Hnrps"    ∷ own_greader_nrps grd.

End repr.
