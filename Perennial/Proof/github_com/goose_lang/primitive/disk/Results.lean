/-
The further specs of the disk FFI wrappers `disk.Write` and `disk.Read`, beside the
ordinary triples `wp_Write`/`wp_Read` (`Link`).

The logically atomic specs `wp_Write_atomic`/`wp_Read_atomic` use the
`atomic_fupd` notation (`Perennial.ProgramLogic.AtomicFupd`). The updates in
those specs and in `wp_Write_triple`/`wp_Read_triple` are plain fancy updates,
since there is no crash logic. The ordinary triples `wp_Write`/`wp_Read` are
proved directly from the disk FFI lifting lemmas `wp_ReadOp`/`wp_WriteOp`
rather than derived from the atomic specs; the atomic specs are proved here the same
way, and `wp_Write_triple`/`wp_Read_triple` are derived from them. `wp_Write'` and
`wp_Read_eq` are variants of `wp_Write`/`wp_Read`.
-/
module

public import Perennial.ProgramLogic.AtomicFupd
public import Perennial.Proof.github_com.goose_lang.primitive.disk.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode disk_ffi

namespace github_com.goose_lang.primitive.disk

section results
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

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

theorem wp_Write' (z : Int) (a : w64) (s : GoSlice) (q : DFrac) (b : _root_.Perennial.Block) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive.disk ∗
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


end results

end github_com.goose_lang.primitive.disk

end Perennial
