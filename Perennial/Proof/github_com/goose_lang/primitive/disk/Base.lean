/-
Shared definitions of the proofs of the disk FFI wrappers `disk.Read`, `disk.Write` and
`disk.Barrier` (`github.com/goose-lang/primitive/disk`): its `isPkgInit`, `listToBlock`,
`isBlock`/`isBlockFull`, the lemmas relating slices and disk blocks, and the atomicity of
the disk FFI operations.
-/
module

public import Perennial.Proof.DiskPrelude
public import Perennial.ProgramLogic.AtomicFupd
public import Perennial.Code.github_com.goose_lang.primitive.disk
public import Perennial.GeneratedProof.github_com.goose_lang.primitive.disk

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode disk_ffi

namespace github_com.goose_lang.primitive.disk

def listToBlock (l : List w8) : _root_.Perennial.Block :=
  if h : l.length = blockBytes then ⟨l.toArray, by simpa using h⟩ else Vector.replicate _ 0

theorem listToBlock_to_list (l : List w8) (h : l.length = blockBytes) :
    (listToBlock l).toList = l := by
  simp [listToBlock, h]

theorem block_list_inj (l : List w8) (b : _root_.Perennial.Block) (h : l = b.toList) : b = listToBlock l := by
  subst h
  apply Vector.toList_inj.mp
  rw [listToBlock_to_list _ (by simp)]

theorem block_to_list_to_block (i : _root_.Perennial.Block) : listToBlock i.toList = i :=
  (block_list_inj _ _ rfl).symm

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.primitive.disk :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.primitive.disk :=
  build_get_is_pkg_init_wf

def isBlock (s : GoSlice) (dq : DFrac) (b : _root_.Perennial.Block) : IProp GF := s ↦*{dq} b.toList

def isBlockFull (s : GoSlice) (b : _root_.Perennial.Block) : IProp GF := s ↦* b.toList

instance isBlock_timeless (s : GoSlice) (q : DFrac) (b : _root_.Perennial.Block) :
    Timeless (isBlock (GF := GF) s q b) := by
  unfold isBlock; rw [ownSlice_unseal]; unfold ownSliceDef; infer_instance

instance isBlock_dfractional (s : GoSlice) (b : _root_.Perennial.Block) :
    DFractional (fun dq => isBlock (GF := GF) s dq b) := by
  unfold isBlock; infer_instance

theorem listToBlock_to_vals (l : List w8) (h : l.length = blockBytes) :
    BlockToVals (listToBlock l) = l.map (fun b => (#b : val)) := by
  rw [BlockToVals, listToBlock_to_list _ h]

/-- The element points-tos of a byte array are heap points-tos. -/
theorem arrayElems_w8 (l : Loc) (vs : List w8) (dq : DFrac) :
    arrayElems (GF := GF) l vs dq ⊣⊢
      [∗list] i ↦ v ∈ vs.map (fun b => (#b : val)), heapPointsto (l +ₗ (i : Int)) dq v := by
  unfold arrayElems
  rw [BigSepL.bigSepL_map]
  constructor
  · apply BigSepL.bigSepL_mono
    intro k x _
    rw [go.arrayIndexRef_add_loc_add, typedPointsto_unseal_eq, typedPointstoDef_heap]
    iintro ⟨H, _⟩; iexact H
  · apply BigSepL.bigSepL_mono
    intro k x _
    rw [go.arrayIndexRef_add_loc_add, typedPointsto_unseal_eq, typedPointstoDef_heap]
    iintro H
    ihave %Hnn := heapPointsto_non_null _ _ _ $$ H
    iframe H; ipureintro; exact Hnn

theorem slice_to_block_array (s : GoSlice) (dq : DFrac) (b : _root_.Perennial.Block) :
    s ↦*{dq} b.toList ⊢ pointstoBlock (GF := GF) s.ptr dq b := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exfalso
    have h := congrArg List.length H.2
    rw [Vector.length_toList] at h
    simp [blockBytes] at h
  · rw [typedPointsto_unseal_eq]
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨⟨_, Ha⟩, _⟩
    unfold pointstoBlock BlockToVals
    iapply (arrayElems_w8 s.ptr b.toList dq).1 $$ Ha

theorem block_array_to_slice (s : GoSlice) (dq : DFrac) (b : _root_.Perennial.Block)
    (hlen : b.toList.length = sint.nat s.len) (hcap : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap) :
    pointstoBlock (GF := GF) s.ptr dq b ⊢ s ↦*{dq} b.toList := by
  iintro Hb
  ihave %Hnn : (⌜s.ptr ≠ null⌝ : IProp GF) $$ [Hb]
  · unfold pointstoBlock BlockToVals
    obtain ⟨⟨l⟩, hl⟩ := b
    cases l with
    | nil => simp [blockBytes] at hl
    | cons x xs =>
      simp only [Vector.toList_mk, List.map_cons]
      icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨H0, _⟩
      rw [show ((0 : Nat) : Int) = 0 from rfl, loc_add_0] at *
      iapply heapPointsto_non_null $$ H0
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  rw [typedPointsto_unseal_eq]
  simp only [TypedPointsto.typedPointstoDef]
  unfold pointstoBlock BlockToVals
  isplitl
  · isplitl
    · isplitr
      · ipureintro; simp only [sint.nat, sint.Z] at *; omega
      · iapply (arrayElems_w8 s.ptr b.toList dq).2 $$ Hb
    · ipureintro; exact Hnn
  · ipureintro; exact hcap.2

theorem block_array_to_slice_mk (l : Loc) (dq : DFrac) (b : _root_.Perennial.Block) :
    pointstoBlock (GF := GF) l dq b ⊢
      slice.mk l (W64 b.toList.length) (W64 b.toList.length) ↦*{dq} b.toList := by
  rw [Vector.length_toList]
  exact block_array_to_slice (slice.mk l (W64 blockBytes) (W64 blockBytes)) dq b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩

theorem slice_to_block (s : GoSlice) (dq : DFrac) (bs : List w8) (Hsz : s.len = W64 4096) :
    s ↦*{dq} bs ⊢ pointstoBlock (GF := GF) s.ptr dq (listToBlock bs) := by
  iintro Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have hl : bs.length = blockBytes := by rw [Hlen.1, Hsz]; rfl
  rw [← listToBlock_to_list bs hl] at *
  rw [block_to_list_to_block]
  iapply slice_to_block_array $$ Hs

/-! Atomicity of the disk FFI operations. -/

open EctxLanguage in
instance ReadOp_atomic (at' : Language.Atomicity) (v : val) :
    Language.Atomic at' (ExternalOp DiskOp.ReadOp (Val v)) :=
  goose_atomic at'
    (fun _ _ _ _ _ h => by
      cases h with
      | ExternalOpS _ _ _ _ _ H =>
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := diskFfiStep_ReadOp_inv H; rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

open EctxLanguage in
instance WriteOp_atomic (at' : Language.Atomicity) (v : val) :
    Language.Atomic at' (ExternalOp DiskOp.WriteOp (Val v)) :=
  goose_atomic at'
    (fun _ _ _ _ _ h => by
      cases h with
      | ExternalOpS _ _ _ _ _ H =>
        obtain ⟨_, _, _, _, _, _, _, rfl, _⟩ := diskFfiStep_WriteOp_inv H; rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fillItem] at h <;> cases h <;> rfl)

end wps

end github_com.goose_lang.primitive.disk

end Perennial
end
