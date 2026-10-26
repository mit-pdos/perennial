/-
The extensions of a networked program with a filesystem: the closed list
`[fsExt, netExt]` (`fsNetExts`), its semantics and ghost state, and ghost
state `fsNetGF` for it.

A distributed program over these extensions is closed off by the distributed
adequacy theorem `goose_dist_adequacy` (`DistAdequacy.lean`) with these
instances; `fsNetGF` has a slot for each camera that `GooseGpreS` needs, so that
a client's theorem need not assume any. The start resources of `[fsExt, netExt]`
are the network's points-to (`fsNet_globalStart`) and, for a node, its files'
points-to and its address (`fsNet_localStart`).
-/
module

public import Perennial.GooseLang.DistAdequacy
public import Perennial.GooseLang.Ext.Fs.Specs
public import Perennial.GooseLang.Ext.Net.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a networked program with a filesystem. -/
@[reducible] def fsNetExts : GooseExts := ⟨[fsExt, netExt]⟩

attribute [local instance] fsNetExts

@[reducible] def fsNetExtsSemantics : GooseSemantics := ⟨(fs_semantics, net_semantics, ⟨⟩)⟩

@[reducible] def fsNetExtsInterp : GooseInterp := ⟨(fs_interp, net_interp, ⟨⟩)⟩

attribute [local instance] fsNetExtsSemantics fsNetExtsInterp

@[reducible] def fsNetExts_hasFs : HasExt fsExt where
  mem := .here
  sem_eq := rfl
  interp_eq := rfl

@[reducible] def fsNetExts_hasNet : HasExt netExt where
  mem := .there .here
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] fsNetExts_hasFs fsNetExts_hasNet

/-- Ghost state for a networked program with a filesystem: one slot for each
camera that `GooseGpreS` needs for `[fsExt, netExt]` (the network's message sets
share the filesystem's ghost names and meta data slots). -/
noncomputable def fsNetGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨constOF (HeapView GoString (Agree (DiscreteO (List w8))) (GMap GoString)), inferInstance⟩
  | 8 => ⟨constOF (HeapView GoString (Agree (DiscreteO GName)) (GMap GoString)), inferInstance⟩
  | 9 => ⟨constOF MetaUR, inferInstance⟩
  | 10 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 11 => ⟨constOF (HeapView GoString (Agree (DiscreteO (GSet NetMsg))) (GMap GoString)),
      inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance fsNetGpreS : GooseGpreS fsNetGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨⟨⟨7, rfl⟩⟩, ⟨⟨8, rfl⟩⟩, ⟨9, rfl⟩⟩,
    ⟨⟨⟨11, rfl⟩⟩, ⟨⟨8, rfl⟩⟩, ⟨9, rfl⟩⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨10, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The global start resources of `[fsExt, netExt]`: the network's points-to. -/
theorem fsNet_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢
      [∗map] a ↦ ms ∈ extGlobal netExt g, netPointsto (extGlobalGS netExt) a (.own 1) ms :=
  (sep_elim_right (P := iprop(True))).trans sep_elim_left

/-- The local start resources of `[fsExt, netExt]` for a node: its files'
points-to and its address. -/
theorem fsNet_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢
      ([∗map] f ↦ c ∈ extLocal fsExt σ, fsPointsto (extLocalGS fsExt) f (.own 1) c) ∗
      ⌜(extLocalGS netExt (L := L) : NetNodeGS GF).addr = extLocal netExt σ⌝ :=
  sep_mono_right sep_elim_left

end start

end Perennial
