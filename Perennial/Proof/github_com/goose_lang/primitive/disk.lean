/-
Specs for the disk
FFI wrappers `disk.Read`, `disk.Write` and `disk.Barrier`.

The logically atomic specs `wp_Write_atomic`/`wp_Read_atomic` use the
`atomic_fupd` notation (`Perennial.ProgramLogic.AtomicFupd`). The updates in
those specs and in `wp_Write_triple`/`wp_Read_triple` are plain fancy updates,
since there is no crash logic. The ordinary triples `wp_Write`/`wp_Read` are
proved directly from the disk FFI lifting lemmas `wp_ReadOp`/`wp_WriteOp`
rather than derived from the atomic specs.
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
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
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
  unfold isBlock; infer_instance

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

theorem wp_Write_atomic (a : w64) (s : GoSlice) (dq : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        s ↦*{dq} b.toList }}
    <<{ ∀∀ b0, uint.Z a d↦ b0 }>>
      (App (App (Val (@! Write)) (Val #a)) (Val #s)) @@ ∅
    <<{ uint.Z a d↦ b }>>
    {{ RET #(); s ↦*{dq} b.toList }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hpos : sint.Z (W64 0) < sint.Z s.len := by
    rw [Vector.length_toList] at Hlen
    simp only [sint.nat, sint.Z, blockBytes] at *; simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hpos⟩)]
  simp only [sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
  wp_pures
  iapply wp_atomic (E2 := ∅)
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HΦ with ⟨%b0, Hda, Hupd⟩
  imodintro
  wp_apply_core wp_WriteOp a b dq s.ptr $$ [Hda Hs]
  · isplitl [Hda]
    · iexists b0; iexact Hda
    iapply slice_to_block_array $$ Hs
  iintro ⟨Hda, Hl⟩
  imod Hupd $$ Hda with HQ
  imodintro
  iapply HQ
  iapply block_array_to_slice s dq b (by simp only [sint.nat] at *; omega) Hwf $$ Hl

theorem wp_Write_triple (E' : CoPset) (Q : IProp GF) (a : w64) (s : GoSlice) (dq : DFrac)
    (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        s ↦*{dq} b.toList ∗
        (|={⊤,E'}=> ∃ b0, uint.Z a d↦ b0 ∗ (uint.Z a d↦ b -∗ |={E',⊤}=> Q)) }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); s ↦*{dq} b.toList ∗ Q }} := by
  iintro %Φ ⟨#Hpkg, Hs, Hupd⟩ HΦ
  iapply wp_Write_atomic a s dq b $$ [Hs]
  · iframe Hpkg; iexact Hs
  inext
  rw [Iris.Std.LawfulSet.diff_empty]
  imod Hupd with ⟨%b0, Hda, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro HcloseE
  iexists b0
  iframe Hda
  iintro Hda
  imod HcloseE
  imod Hclose $$ Hda with HQ
  imodintro
  iintro Hs
  iapply HΦ
  iframe

theorem wp_Write (a : w64) (s : GoSlice) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        ∃ b0, uint.Z a d↦ b0 ∗ s ↦*{q} b.toList }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); uint.Z a d↦ b ∗ s ↦*{q} b.toList }} := by
  wp_start as ⟨%b0, Hda, Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have hpos : sint.Z (W64 0) < sint.Z s.len := by
    rw [Vector.length_toList] at Hlen
    simp only [sint.nat, sint.Z, blockBytes] at *; simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hpos⟩)]
  simp only [sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
  wp_pures
  wp_apply_core wp_WriteOp a b q s.ptr $$ [Hda Hs]
  · isplitl [Hda]
    · iexists b0; iexact Hda
    iapply slice_to_block_array $$ Hs
  iintro ⟨Hda, Hl⟩
  iapply HΦ
  iframe Hda
  iapply block_array_to_slice s q b (by simp only [sint.nat] at *; omega) Hwf $$ Hl

theorem wp_Write' (z : Int) (a : w64) (s : GoSlice) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        ⌜uint.Z a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ s ↦*{q} b.toList }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); z d↦ b ∗ s ↦*{q} b.toList }} := by
  iintro %Φ ⟨#Hpkg, %Hz, Hpre⟩ HΦ
  subst Hz
  icases Hpre with > ⟨%b0, Hda, Hs⟩
  iapply wp_Write a s q b $$ [Hda Hs] HΦ
  iframe Hpkg
  iexists b0
  iframe

theorem wp_Read_atomic (a : w64) (q : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk }}
    <<{ ∀∀ b, uint.Z a d↦{q} b }>>
      (App (Val (@! Read)) (Val #a)) @@ ∅
    <<{ uint.Z a d↦{q} b }>>
    {{ (s : GoSlice), RET #s; isBlockFull s b }} := by
  wp_start
  wp_bind (ExternalOp _ _)
  iapply wp_atomic (E2 := ∅)
  rw [Iris.Std.LawfulSet.diff_empty]
  imod HΦ with ⟨%b, Hda, Hupd⟩
  imodintro
  wp_apply_core wp_ReadOp a q b $$ [Hda]
  · iexact Hda
  iintro %l ⟨Hda, Hl⟩
  imod Hupd $$ Hda with HQ
  imodintro
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
  wp_pures
  iapply HQ
  unfold isBlockFull
  iapply block_array_to_slice (slice.mk l (W64 4096) (W64 4096)) (DFrac.own 1) b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩ $$ Hl

theorem wp_Read_triple (E' : CoPset) (Q : _root_.Perennial.Block → IProp GF) (a : w64) (q : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        |={⊤,E'}=> ∃ b, uint.Z a d↦{q} b ∗ (uint.Z a d↦{q} b -∗ |={E',⊤}=> Q b) }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : GoSlice) (b : _root_.Perennial.Block), RET #s; Q b ∗ isBlockFull s b }} := by
  iintro %Φ ⟨#Hpkg, Hupd⟩ HΦ
  iapply wp_Read_atomic a q $$ []
  · iexact Hpkg
  inext
  rw [Iris.Std.LawfulSet.diff_empty]
  imod Hupd with ⟨%b0, Hda, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro HcloseE
  iexists b0
  iframe Hda
  iintro Hda
  imod HcloseE
  imod Hclose $$ Hda with HQ
  imodintro
  iintro %s Hs
  iapply HΦ
  iframe

theorem wp_Read (a : w64) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        uint.Z a d↦{q} b }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : GoSlice), RET #s; uint.Z a d↦{q} b ∗ isBlockFull s b }} := by
  wp_start as Hda
  wp_bind (ExternalOp _ _)
  wp_apply_core wp_ReadOp a q b $$ [Hda]
  · iexact Hda
  iintro %l ⟨Hda, Hl⟩
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
  wp_pures
  iapply HΦ
  iframe Hda
  unfold isBlockFull
  iapply block_array_to_slice (slice.mk l (W64 4096) (W64 4096)) (DFrac.own 1) b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩ $$ Hl

theorem wp_Read_eq (a : w64) (a' : Int) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        a' d↦{q} b ∗ ⌜uint.Z a = a'⌝ }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : GoSlice), RET #s; a' d↦{q} b ∗ isBlockFull s b }} := by
  iintro %Φ ⟨#Hpkg, Hb, %Heq⟩ HΦ
  subst Heq
  iapply wp_Read a q b $$ [Hb] HΦ
  iframe Hb
  iframe #

theorem wp_Barrier :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk }}
      (App (Val (@! Barrier)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

end github_com.goose_lang.primitive.disk

end Perennial
end
