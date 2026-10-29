/-
The proof of `writeInlineBucket`: the bucket header over the first 16 bytes of a new zeroed slice,
then a leaf page after it, as in `writeLeaf`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket.wp_proof
    (wp_pageSize : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize.spec (GF := GF) (hG := hG))
    (wp_writeInodeToPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket.spec (GF := GF) (hG := hG) := by
  intro b bkt dq s ms
  wp_start as ⟨Hb, #Hin, %Hfit⟩
  wp_auto
  wp_apply wp_pageSize s ms $$ [Hin]
  · iexact Hin
  have hbody := pageBody_length true ms
  obtain ⟨_, hB32, _⟩ := Hfit
  generalize hL : (pageBody true ms).length = L at *
  simp only [bucketHeaderSize]
  rw [show W64 16 + W64 ((16 + L : Nat) : Int) = W64 ((32 + L : Nat) : Int) by push_cast; word]
  have hNZ : sint.Z (W64 ((32 + L : Nat) : Int)) = ((32 + L : Nat) : Int) := sint_Z_W64_nat _ (by omega)
  wp_apply wp_slice_make2 (V := w8) $$ [] as %val ⟨Hv, -⟩
  · ipureintro; rw [hNZ]; omega
  rw [show sint.nat (W64 ((32 + L : Nat) : Int)) = 32 + L by simp only [sint.nat, hNZ]; omega]
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  ihave %Hvp := ownSlice_ptr_pos _ _ _ (by simp) $$ Hv
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hvp $$ Hv
    with ⟨Hbytes, Hback⟩
  rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
  have hvlen : sint.Z val.len = ((32 + L : Nat) : Int) :=
    sint_Z_eq_of_sint_nat _ _ (by simpa using Hvl.1) Hvl.2
  simp only [hvlen, show sint.Z (W64 0) = 0 from rfl,
    show (0 : Int) ≤ 0 ∧ (0 : Int) < ((32 + L : Nat) : Int) from ⟨Int.le_refl _, by omega⟩]
  rw [show sliceIndexRef w8 0 val = val.ptr by rw [sliceIndexRef_byte _ _ Hvp (Int.le_refl _)]; simp]
  rw [show List.replicate (32 + L) (0 : w8) = List.replicate 16 0 ++ (List.replicate 16 0 ++
    List.replicate L 0) by
      rw [List.replicate_append_replicate, List.replicate_append_replicate]; congr 1; omega]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hbytes with ⟨Hh0, Hbytes⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hbytes with ⟨Hh1, Hbytes⟩
  icases (bytesPointsto_typed (V := InBucket) _ _ _ (by simp) Hvp).1 $$ Hh0 with Hh0
  rw [List.length_replicate] at *
  have hp16 : 0 < (val.ptr +ₗ ((16 : Nat) : Int)).addr := by simp [Loc.add]; omega
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) hp16).1 $$ Hh1 with Hh1
  wp_auto
  simp only [hvlen, show sint.Z (W64 16) = 16 from rfl,
    show (0 : Int) ≤ 16 ∧ (16 : Int) < ((32 + L : Nat) : Int) from ⟨by decide, by omega⟩]
  rw [show sliceIndexRef w8 16 val = val.ptr +ₗ ((16 : Nat) : Int) by
    rw [sliceIndexRef_byte _ _ Hvp (by decide)]; rfl]
  wp_auto
  unfold inodesOwn
  icases Hin with ⟨%xs, #Hs, #Hxs⟩
  ihave %Hl1 := BigSepL2.bigSepL2_length $$ Hxs
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hs
  have hsZ : sint.Z s.len = ms.length := sint_Z_eq_of_sint_nat _ _ (Hl1 ▸ Hl2.1) Hl2.2
  ihave Hh1 := typedPointsto_of_eq _ _ (leafHeader ms) _ $$ [Hh1]
  · iframe Hh1
    ipureintro
    simp only [leafHeader, hsZ]
    rfl
  rw [show ((16 : Nat) : Int) = 16 from rfl]
  wp_apply wp_writeInodeToPage s ms (val.ptr +ₗ 16) (leafHeader ms) L $$ [Hh1 Hbytes] as %w ⟨Hh1, Hbytes⟩
  · iframe Hh1 Hbytes
    isplitl
    · unfold inodesOwn; iexists xs; iframe Hs Hxs
    · ipureintro; exact ⟨hp16, ⟨by omega, by omega, by assumption⟩, by omega⟩
  rw [pageIsLeaf_leafHeader, hL, Nat.sub_self, List.replicate_zero, List.append_nil]
  icases (typedPointsto_bytes (V := InBucket) _ _ _ Hvp).1 $$ Hh0 with Hh0
  icases (typedPointsto_bytes (V := Page) _ _ _ hp16).1 $$ Hh1 with Hh1
  iapply HΦ
  iframe Hb
  iapply Hback
  · ipureintro; simp [ByteEncoding.encode_length, hL]; omega
  rw [flatMap_encode_w8, List.append_assoc]
  iapply (bytesPointsto_app _ _ _ _).2
  iframe Hh0
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length, ByteEncoding.encode_length,
    show ((16 : Nat) : Int) = 16 from rfl]
  iframe

end proof

end Perennial
