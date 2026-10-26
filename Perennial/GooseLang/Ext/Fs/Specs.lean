/-
Iris reasoning principles for the filesystem extension.

Notes:
* The ghost state is a `genHeapGS` from file names to contents: `f fs↦{q} c`
  says that the file `f` has contents `c`. It is per generation (`LocalGS`);
  its crash behaviour, for the crash adequacy theorem, is in
  `Perennial/GooseLang/Ext/Fs/Adequacy.lean`.
* The specs hold for any program whose extensions include the filesystem
  (`HasExt fsExt`), with an injective encoding of strings as values (as the Go
  model's `go.BasicIntoValInj` has). They are standard WP specs; there is no
  crash reasoning.
-/
module

public import Iris.BI.Lib.GenHeap
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Ext.Fs.Impl
public import Perennial.GooseLang.Ext.GenHeap
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Ghost state -/

class FsGpreS (GF : BundledGFunctors) where
  fsPreGHeapG : genHeapPreS GoString (List w8) GF (GMap GoString)

class FsGS (GF : BundledGFunctors) where
  fsHeapG : genHeapGS GoString (List w8) GF (GMap GoString)

section fs
variable {GF : BundledGFunctors}

/-- The interpretation of the files. -/
def fsCtx (hL : FsGS GF) (fs : FsState) : IProp GF :=
  genHeapInterp (G := hL.fsHeapG) fs

/-- The file `f` has contents `c`. -/
def fsPointsto (hL : FsGS GF) (f : GoString) (q : DFrac) (c : List w8) : IProp GF :=
  pointsTo (G := hL.fsHeapG) f q c

instance fsPointsto_timeless (hL : FsGS GF) (f : GoString) (q : DFrac) (c : List w8) :
    Timeless (fsPointsto hL f q c) := by
  unfold fsPointsto; infer_instance

instance fsPointsto_persistent (hL : FsGS GF) (f : GoString) (c : List w8) :
    Persistent (fsPointsto hL f .discard c) := by
  unfold fsPointsto; infer_instance

theorem fs_local_init (hPre : FsGpreS GF) (fs : FsState) :
    ⊢@{IProp GF} |==> ∃ hL : FsGS GF, fsCtx hL fs ∗
      [∗map] f ↦ c ∈ fs, fsPointsto hL f (.own 1) c := by
  letI := hPre.fsPreGHeapG
  imod genHeap_init (H := GMap GoString) fs with ⟨%names, H1, H2, -⟩
  imodintro
  iexists (⟨names⟩ : FsGS GF)
  isplitl [H1]
  · unfold fsCtx; iexact H1
  · unfold fsPointsto; iexact H2

end fs

/-- The ghost state of the filesystem. The program gets ownership of the
initial files. -/
instance fs_interp : ExtInterp fsExt where
  LocalGS := FsGS
  GlobalGS _ := Unit
  localCtx := fsCtx
  globalCtx _ _ := iprop(True)
  PreG := FsGpreS
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart hL fs := iprop([∗map] f ↦ c ∈ fs, fsPointsto hL f (.own 1) c)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ hPre fs _ _ := fs_local_init hPre fs

/-! ## Specs -/

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [GoGlobalContext]
  [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseFsGS : FsGS GF := extLocalGS fsExt

/- Notations `f fs↦{q} c`, `f fs↦ c` and `f fs↦□ c`. -/
namespace fs_ext
scoped notation:50 f:51 " fs↦{" q "} " c:50 => fsPointsto gooseFsGS f q c
scoped notation:50 f:51 " fs↦ " c:50 => fsPointsto gooseFsGS f (DFrac.own 1) c
scoped notation:50 f:51 " fs↦□ " c:50 => fsPointsto gooseFsGS f DFrac.discard c
end fs_ext
open fs_ext

theorem fs_local_ctx_eq (fs : FsState) :
    ExtInterp.localCtx (E := fsExt) (extLocalGS fsExt) fs ⊣⊢
      genHeapInterp (G := (gooseFsGS (L := L)).fsHeapG) fs := .rfl

theorem wp_FsRead (f : GoString) (q : DFrac) (c : List w8) :
    {{ (f fs↦{q} c : IProp GF) }} (ExternalOp (extOp fsExt FsOp.ReadOp) (Val (#f))) @ s; E
    {{ RET #c; f fs↦{q} c }} := by
  iintro %Φ Hc HΦ
  iapply wp_extStep FsOp.ReadOp (#f) Φ (by simp)
  iintro %h %fs %g Hheap Hl Hg
  icases (fs_local_ctx_eq fs).mp $$ Hl with Hl
  unfold fsPointsto
  icases genHeap_lookup (G := (gooseFsGS (L := L)).fsHeapG) $$ Hl Hc with %Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, fs, g, rfl, f, c, rfl, Heq, rfl, rfl⟩
  inext
  iintro %e' %h' %fs' %g' %Hst _
  obtain ⟨rfl, f', c', Hv, Hc', rfl, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj Hv
  change fs' !! f = some c at Heq
  rw [Heq] at Hc'
  cases Hc'
  imod Hclose
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (fs_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_FsWrite (f : GoString) (old new : List w8) :
    {{ (f fs↦ old : IProp GF) }}
      (ExternalOp (extOp fsExt FsOp.WriteOp) (Val (PairV (#f) (#new)))) @ s; E
    {{ RET #(); f fs↦ new }} := by
  iintro %Φ Hc HΦ
  iapply wp_extStep FsOp.WriteOp (PairV (#f) (#new)) Φ (by simp [val.isPanic])
  iintro %h %fs %g Hheap Hl Hg
  icases (fs_local_ctx_eq fs).mp $$ Hl with Hl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, _, g, rfl, f, new, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %fs' %g' %Hst _
  obtain ⟨rfl, f', new', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hf, Hnew⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj Hf
  obtain rfl := go.intoVal_inj (V := List w8) Hnew
  unfold fsPointsto
  imod genHeap_update' (G := (gooseFsGS (L := L)).fsHeapG) (v₂ := new) $$ [Hl Hc]
    with ⟨Hl, Hc⟩
  · iframe
  imod Hclose
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (fs_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iapply HΦ
  iexact Hc

/-- `wp_FsRead` as a logically atomic spec: the file's points-to is needed only
during the step, so it can come from an invariant. -/
theorem wp_FsRead_atomic (f : GoString) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ (q : DFrac) (c : List w8), f fs↦{q} c ∗ (f fs↦{q} c ={∅,E}=∗ Φ #c))
    ⊢ WP (ExternalOp (extOp fsExt FsOp.ReadOp) (Val (#f))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep FsOp.ReadOp (#f) Φ (by simp)
  iintro %h %fs %g Hheap Hl Hg
  imod HAU with ⟨%q, %c, Hc, Hclose⟩
  icases (fs_local_ctx_eq fs).mp $$ Hl with Hl
  unfold fsPointsto
  icases genHeap_lookup (G := (gooseFsGS (L := L)).fsHeapG) $$ Hl Hc with %Heq
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, fs, g, rfl, f, c, rfl, Heq, rfl, rfl⟩
  inext
  iintro %e' %h' %fs' %g' %Hst _
  obtain ⟨rfl, f', c', Hv, Hc', rfl, rfl⟩ := Hst
  obtain rfl := go.intoVal_inj Hv
  change fs' !! f = some c at Heq
  rw [Heq] at Hc'
  cases Hc'
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (fs_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

/-- `wp_FsWrite` as a logically atomic spec. -/
theorem wp_FsWrite_atomic (f : GoString) (new : List w8) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ old : List w8, f fs↦ old ∗ (f fs↦ new ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp (extOp fsExt FsOp.WriteOp) (Val (PairV (#f) (#new)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_extStep FsOp.WriteOp (PairV (#f) (#new)) Φ (by simp [val.isPanic])
  iintro %h %fs %g Hheap Hl Hg
  imod HAU with ⟨%old, Hc, Hclose⟩
  icases (fs_local_ctx_eq fs).mp $$ Hl with Hl
  imodintro
  isplitr
  · ipureintro; exact ⟨_, h, _, g, rfl, f, new, rfl, rfl, rfl⟩
  inext
  iintro %e' %h' %fs' %g' %Hst _
  obtain ⟨rfl, f', new', Hv, rfl, rfl⟩ := Hst
  obtain ⟨Hf, Hnew⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj Hf
  obtain rfl := go.intoVal_inj (V := List w8) Hnew
  unfold fsPointsto
  imod genHeap_update' (G := (gooseFsGS (L := L)).fsHeapG) (v₂ := new) $$ [Hl Hc]
    with ⟨Hl, Hc⟩
  · iframe
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hheap Hg
  isplitl [Hl]
  · iapply (fs_local_ctx_eq _).mpr; iexact Hl
  iapply wp_value'
  iexact HΦ

/-- A file's points-to can be made persistent: the file will not be written
any more. -/
theorem fsPointsto_persist (f : GoString) (q : DFrac) (c : List w8) :
    ⊢@{IProp GF} f fs↦{q} c ==∗ f fs↦□ c := by
  unfold fsPointsto
  letI := (gooseFsGS (L := L)).fsHeapG
  exact pointsTo_persist

end lifting

end Perennial
