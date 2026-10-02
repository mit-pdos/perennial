/-
Port of `new/proof/github_com/goose_lang/primitive/disk.v`: specs for the disk
FFI wrappers `disk.Read`, `disk.Write` and `disk.Barrier`.

The logically atomic specs `wp_Write_atomic`/`wp_Read_atomic` use the
`atomic_fupd` notation (`Perennial.ProgramLogic.AtomicFupd`). Rocq's non-crash
fancy updates `|NC={..}=>` (in those specs and in `wp_Write_triple`/
`wp_Read_triple`) are plain fancy updates here, since the port has no crash
logic. The ordinary triples `wp_Write`/`wp_Read` are proved directly from the
disk FFI lifting lemmas `wp_ReadOp`/`wp_WriteOp` rather than derived from the
atomic specs as in Rocq.
-/
import Perennial.Proof.DiskPrelude
import Perennial.ProgramLogic.AtomicFupd
import Perennial.Code.github_com.goose_lang.primitive.disk
import Perennial.GeneratedProof.github_com.goose_lang.primitive.disk

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode disk_ffi

namespace github_com.goose_lang.primitive.disk

/-- Rocq `list_to_block`. -/
def list_to_block (l : List w8) : _root_.Perennial.Block :=
  if h : l.length = block_bytes then ⟨l.toArray, by simpa using h⟩ else Vector.replicate _ 0

theorem list_to_block_to_list (l : List w8) (h : l.length = block_bytes) :
    (list_to_block l).toList = l := by
  simp [list_to_block, h]

theorem block_list_inj (l : List w8) (b : _root_.Perennial.Block) (h : l = b.toList) : b = list_to_block l := by
  subst h
  apply Vector.toList_inj.mp
  rw [list_to_block_to_list _ (by simp)]

theorem block_to_list_to_block (i : _root_.Perennial.Block) : list_to_block i.toList = i :=
  (block_list_inj _ _ rfl).symm

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.primitive.disk :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.primitive.disk :=
  build_get_is_pkg_init_wf

def is_block (s : slice.t) (dq : DFrac) (b : _root_.Perennial.Block) : IProp GF := s ↦*{dq} b.toList

def is_block_full (s : slice.t) (b : _root_.Perennial.Block) : IProp GF := s ↦* b.toList

instance is_block_timeless (s : slice.t) (q : DFrac) (b : _root_.Perennial.Block) :
    Timeless (is_block (GF := GF) s q b) := by
  unfold is_block; rw [own_slice_unseal]; unfold own_slice_def; infer_instance

instance is_block_dfractional (s : slice.t) (b : _root_.Perennial.Block) :
    DFractional (fun dq => is_block (GF := GF) s dq b) := by
  unfold is_block; infer_instance

theorem list_to_block_to_vals (l : List w8) (h : l.length = block_bytes) :
    Block_to_vals (list_to_block l) = l.map (fun b => (#b : val)) := by
  rw [Block_to_vals, list_to_block_to_list _ h]

/-- The element points-tos of a byte array are heap points-tos. -/
theorem array_elems_w8 (l : loc) (vs : List w8) (dq : DFrac) :
    array_elems (GF := GF) l vs dq ⊣⊢
      [∗list] i ↦ v ∈ vs.map (fun b => (#b : val)), heap_pointsto (l +ₗ (i : Int)) dq v := by
  unfold array_elems
  rw [BigSepL.bigSepL_map]
  constructor
  · apply BigSepL.bigSepL_mono
    intro k x _
    rw [go.array_index_ref_add_loc_add, typed_pointsto_unseal_eq, typed_pointsto_def_heap]
    iintro ⟨H, _⟩; iexact H
  · apply BigSepL.bigSepL_mono
    intro k x _
    rw [go.array_index_ref_add_loc_add, typed_pointsto_unseal_eq, typed_pointsto_def_heap]
    iintro H
    ihave %Hnn := heap_pointsto_non_null _ _ _ $$ H
    iframe H; ipureintro; exact Hnn

theorem slice_to_block_array (s : slice.t) (dq : DFrac) (b : _root_.Perennial.Block) :
    s ↦*{dq} b.toList ⊢ pointsto_block (GF := GF) s.ptr dq b := by
  rw [own_slice_unseal]; unfold own_slice_def
  iintro (%H | ⟨H, %_⟩)
  · exfalso
    have h := congrArg List.length H.2
    rw [Vector.length_toList] at h
    simp [block_bytes] at h
  · rw [typed_pointsto_unseal_eq]
    simp only [TypedPointsto.typed_pointsto_def]
    icases H with ⟨⟨_, Ha⟩, _⟩
    unfold pointsto_block Block_to_vals
    iapply (array_elems_w8 s.ptr b.toList dq).1 $$ Ha

theorem block_array_to_slice (s : slice.t) (dq : DFrac) (b : _root_.Perennial.Block)
    (hlen : b.toList.length = sint.nat s.len) (hcap : 0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap) :
    pointsto_block (GF := GF) s.ptr dq b ⊢ s ↦*{dq} b.toList := by
  iintro Hb
  ihave %Hnn : (⌜s.ptr ≠ null⌝ : IProp GF) $$ [Hb]
  · unfold pointsto_block Block_to_vals
    obtain ⟨⟨l⟩, hl⟩ := b
    cases l with
    | nil => simp [block_bytes] at hl
    | cons x xs =>
      simp only [Vector.toList_mk, List.map_cons]
      icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨H0, _⟩
      rw [show ((0 : Nat) : Int) = 0 from rfl, loc_add_0] at *
      iapply heap_pointsto_non_null $$ H0
  rw [own_slice_unseal]; unfold own_slice_def
  iright
  rw [typed_pointsto_unseal_eq]
  simp only [TypedPointsto.typed_pointsto_def]
  unfold pointsto_block Block_to_vals
  isplitl
  · isplitl
    · isplitr
      · ipureintro; simp only [sint.nat, sint.Z] at *; omega
      · iapply (array_elems_w8 s.ptr b.toList dq).2 $$ Hb
    · ipureintro; exact Hnn
  · ipureintro; exact hcap.2

theorem block_array_to_slice_mk (l : loc) (dq : DFrac) (b : _root_.Perennial.Block) :
    pointsto_block (GF := GF) l dq b ⊢
      slice.mk l (W64 b.toList.length) (W64 b.toList.length) ↦*{dq} b.toList := by
  rw [Vector.length_toList]
  exact block_array_to_slice (slice.mk l (W64 block_bytes) (W64 block_bytes)) dq b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩

theorem slice_to_block (s : slice.t) (dq : DFrac) (bs : List w8) (Hsz : s.len = W64 4096) :
    s ↦*{dq} bs ⊢ pointsto_block (GF := GF) s.ptr dq (list_to_block bs) := by
  iintro Hs
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  have hl : bs.length = block_bytes := by rw [Hlen.1, Hsz]; rfl
  rw [← list_to_block_to_list bs hl] at *
  rw [block_to_list_to_block]
  iapply slice_to_block_array $$ Hs

/-! Atomicity of the disk FFI operations (Rocq proves these inline with
`solve_atomic`). -/

open EctxLanguage in
instance ReadOp_atomic (at' : Language.Atomicity) (v : val) :
    Language.Atomic at' (ExternalOp DiskOp.ReadOp (Val v)) :=
  goose_atomic at'
    (fun _ _ _ _ _ h => by
      cases h with
      | ExternalOpS _ _ _ _ _ H =>
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := disk_ffi_step_ReadOp_inv H; rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fill_item] at h <;> cases h <;> rfl)

open EctxLanguage in
instance WriteOp_atomic (at' : Language.Atomicity) (v : val) :
    Language.Atomic at' (ExternalOp DiskOp.WriteOp (Val v)) :=
  goose_atomic at'
    (fun _ _ _ _ _ h => by
      cases h with
      | ExternalOpS _ _ _ _ _ H =>
        obtain ⟨_, _, _, _, _, _, _, rfl, _⟩ := disk_ffi_step_WriteOp_inv H; rfl)
    (by intro Ki e' h; cases Ki <;> simp only [fill_item] at h <;> cases h <;> rfl)

theorem wp_Write_atomic (a : w64) (s : slice.t) (dq : DFrac) (b : _root_.Perennial.Block) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        s ↦*{dq} b.toList }}
    <<{ ∀∀ b0, uint.Z a d↦ b0 }>>
      (App (App (Val (@! Write)) (Val #a)) (Val #s)) @@ ∅
    <<{ uint.Z a d↦ b }>>
    {{ RET #(); s ↦*{dq} b.toList }} := by
  wp_start as Hs
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  have hpos : sint.Z (W64 0) < sint.Z s.len := by
    rw [Vector.length_toList] at Hlen
    simp only [sint.nat, sint.Z, block_bytes] at *; simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hpos⟩)]
  simp only [slice_index_ref, show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0]
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

theorem wp_Write_triple (E' : CoPset) (Q : IProp GF) (a : w64) (s : slice.t) (dq : DFrac)
    (b : _root_.Perennial.Block) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
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

theorem wp_Write (a : w64) (s : slice.t) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        ∃ b0, uint.Z a d↦ b0 ∗ s ↦*{q} b.toList }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); uint.Z a d↦ b ∗ s ↦*{q} b.toList }} := by
  wp_start as ⟨%b0, Hda, Hs⟩
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  have hpos : sint.Z (W64 0) < sint.Z s.len := by
    rw [Vector.length_toList] at Hlen
    simp only [sint.nat, sint.Z, block_bytes] at *; simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hpos⟩)]
  simp only [slice_index_ref, show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0]
  wp_pures
  wp_apply_core wp_WriteOp a b q s.ptr $$ [Hda Hs]
  · isplitl [Hda]
    · iexists b0; iexact Hda
    iapply slice_to_block_array $$ Hs
  iintro ⟨Hda, Hl⟩
  iapply HΦ
  iframe Hda
  iapply block_array_to_slice s q b (by simp only [sint.nat] at *; omega) Hwf $$ Hl

theorem wp_Write' (z : Int) (a : w64) (s : slice.t) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        ⌜uint.Z a = z⌝ ∗ ▷ ∃ b0, z d↦ b0 ∗ s ↦*{q} b.toList }}
      (App (App (Val (@! Write)) (Val #a)) (Val #s))
    {{ RET #(); z d↦ b ∗ s ↦*{q} b.toList }} := by
  iintro %Φ ⟨#Hpkg, %Hz, Hpre⟩ HΦ
  subst Hz
  icases Hpre with ⟨%b0, >Hda, >Hs⟩
  iapply wp_Write a s q b $$ [Hda Hs] HΦ
  iframe Hpkg
  iexists b0
  iframe

theorem wp_Read_atomic (a : w64) (q : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk }}
    <<{ ∀∀ b, uint.Z a d↦{q} b }>>
      (App (Val (@! Read)) (Val #a)) @@ ∅
    <<{ uint.Z a d↦{q} b }>>
    {{ (s : slice.t), RET #s; is_block_full s b }} := by
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
  simp only [show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
  wp_pures
  iapply HQ
  unfold is_block_full
  iapply block_array_to_slice (slice.mk l (W64 4096) (W64 4096)) (DFrac.own 1) b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩ $$ Hl

theorem wp_Read_triple (E' : CoPset) (Q : _root_.Perennial.Block → IProp GF) (a : w64) (q : DFrac) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        |={⊤,E'}=> ∃ b, uint.Z a d↦{q} b ∗ (uint.Z a d↦{q} b -∗ |={E',⊤}=> Q b) }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : slice.t) (b : _root_.Perennial.Block), RET #s; Q b ∗ is_block_full s b }} := by
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
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        uint.Z a d↦{q} b }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : slice.t), RET #s; uint.Z a d↦{q} b ∗ is_block_full s b }} := by
  wp_start as Hda
  wp_bind (ExternalOp _ _)
  wp_apply_core wp_ReadOp a q b $$ [Hda]
  · iexact Hda
  iintro %l ⟨Hda, Hl⟩
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.array_index_ref_0,
    show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
  wp_pures
  iapply HΦ
  iframe Hda
  unfold is_block_full
  iapply block_array_to_slice (slice.mk l (W64 4096) (W64 4096)) (DFrac.own 1) b
    (by rw [Vector.length_toList]; rfl) ⟨(by decide : (0 : Int) ≤ sint.Z (W64 4096)), Int.le_refl _⟩ $$ Hl

theorem wp_Read_eq (a : w64) (a' : Int) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
        a' d↦{q} b ∗ ⌜uint.Z a = a'⌝ }}
      (App (Val (@! Read)) (Val #a))
    {{ (s : slice.t), RET #s; a' d↦{q} b ∗ is_block_full s b }} := by
  iintro %Φ ⟨#Hpkg, Hb, %Heq⟩ HΦ
  subst Heq
  iapply wp_Read a q b $$ [Hb] HΦ
  iframe Hb
  iframe #

theorem wp_Barrier :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk }}
      (App (Val (@! Barrier)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

end github_com.goose_lang.primitive.disk

end Perennial
end
