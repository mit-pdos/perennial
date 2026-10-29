/-
The proof of `openInlineBucket`: whether or not the bytes are aligned (`uintptr` of a pointer is an
arbitrary word), the header and the page are the bytes of `value` or of its copy.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket.wp_proof
    (wp_cloneBytes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket.spec (GF := GF) (hG := hG) := by
  intro v bkt rest writable
  wp_start as ⟨#Hv, %Hne⟩
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  ihave %Hvp := ownSlice_ptr_pos _ _ _ (by simp [Hne]) $$ Hv
  have hlen16 : (encode bkt).length = 16 := ByteEncoding.encode_length _
  have hrl : 0 < rest.length := List.length_pos_iff.2 Hne
  have hvZ : sint.Z v.len = ((16 + rest.length : Nat) : Int) :=
    sint_Z_eq_of_sint_nat _ _ (by rw [← Hvl.1, List.length_append, hlen16]) Hvl.2
  wp_auto
  simp only [hvZ, show sint.Z (W64 0) = 0 from rfl,
    show (0 : Int) ≤ 0 ∧ (0 : Int) < ((16 + rest.length : Nat) : Int) from ⟨Int.le_refl _, by omega⟩]
  rw [show sliceIndexRef w8 0 v = v.ptr by rw [sliceIndexRef_byte _ _ Hvp (Int.le_refl _)]; simp]
  wp_auto
  wp_apply wp_ArbitraryInt as %x _
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hvp $$ Hv
    with ⟨Hbytes, -⟩
  rw [flatMap_encode_w8]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hbytes with ⟨Hhd, Hrest⟩
  rw [hlen16]
  have hb0 : (0 : Int) ≤ 0 ∧ (0 : Int) < ((16 + rest.length : Nat) : Int) := ⟨Int.le_refl _, by omega⟩
  have hb16 : (0 : Int) ≤ 16 ∧ (16 : Int) < ((16 + rest.length : Nat) : Int) := ⟨by decide, by omega⟩
  simp only [bucketHeaderSize]
  wp_if_destruct
  · -- aligned: the header is read in place
    icases (bytesPointsto_typed (V := InBucket) _ _ _ hlen16 Hvp).1 $$ Hhd with #Hhd
    rw [ByteEncoding.decode_encode]
    have hidx16 : sliceIndexRef w8 16 v = v.ptr +ₗ ((16 : Nat) : Int) := by
      rw [sliceIndexRef_byte _ _ Hvp (by decide)]; rfl
    have hidx0 : sliceIndexRef w8 0 v = v.ptr := by
      rw [sliceIndexRef_byte _ _ Hvp (Int.le_refl _)]; simp
    cases writable
    · -- read-only: the header in place
      wp_auto
      simp only [hvZ, show sint.Z (W64 0) = 0 from rfl, hb0, _root_.and_self, ite_true, hidx0]
      wp_auto
      simp only [hvZ, show sint.Z (W64 16) = 16 from rfl, hb16, _root_.and_self, ite_true, hidx16]
      wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ite_false]
      iframe Hhd Hrest
      ipureintro; simp [Loc.add]; omega
    · -- writable: a copy of the header
      wp_auto
      simp only [hvZ, show sint.Z (W64 0) = 0 from rfl, hb0, _root_.and_self, ite_true, hidx0]
      wp_auto
      simp only [hvZ, show sint.Z (W64 16) = 16 from rfl, hb16, _root_.and_self, ite_true, hidx16]
      wp_auto
      iapply HΦ
      iframe
      iframe Hrest
      ipureintro; simp [Loc.add]; omega
  · -- unaligned: a copy
    wp_apply wp_cloneBytes v DFrac.discard _ $$ [Hv] as %c ⟨-, Hc⟩
    · iexact Hv
    ihave %Hcl := ownSlice_len _ _ _ $$ Hc
    ihave %Hcp := ownSlice_ptr_pos _ _ _ (by simp [Hne]) $$ Hc
    have hcZ : sint.Z c.len = ((16 + rest.length : Nat) : Int) :=
      sint_Z_eq_of_sint_nat _ _ (by rw [← Hcl.1, List.length_append, hlen16]) Hcl.2
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hcp $$ Hc
      with ⟨Hc, -⟩
    rw [flatMap_encode_w8]
    icases (bytesPointsto_app _ _ _ _).1 $$ Hc with ⟨Hch, Hcr⟩
    rw [hlen16]
    icases (bytesPointsto_typed (V := InBucket) _ _ _ hlen16 Hcp).1 $$ Hch with Hch
    rw [ByteEncoding.decode_encode]
    imod bytesPointsto_persist _ _ _ $$ Hcr with #Hcr
    have hidx16 : sliceIndexRef w8 16 c = c.ptr +ₗ ((16 : Nat) : Int) := by
      rw [sliceIndexRef_byte _ _ Hcp (by decide)]; rfl
    have hidx0 : sliceIndexRef w8 0 c = c.ptr := by
      rw [sliceIndexRef_byte _ _ Hcp (Int.le_refl _)]; simp
    cases writable
    · -- read-only: the header of the copy, made persistent
      imod typedPointsto_persist_view _ _ _ Hcp $$ Hch with #Hch
      wp_auto
      simp only [hcZ, show sint.Z (W64 0) = 0 from rfl, hb0, _root_.and_self, ite_true, hidx0]
      wp_auto
      simp only [hcZ, show sint.Z (W64 16) = 16 from rfl, hb16, _root_.and_self, ite_true, hidx16]
      wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ite_false]
      iframe Hch Hcr
      ipureintro; simp [Loc.add]; omega
    · -- writable: the header of the copy
      wp_auto
      simp only [hcZ, show sint.Z (W64 0) = 0 from rfl, hb0, _root_.and_self, ite_true, hidx0]
      wp_auto
      simp only [hcZ, show sint.Z (W64 16) = 16 from rfl, hb16, _root_.and_self, ite_true, hidx16]
      wp_auto
      iapply HΦ
      iframe
      iframe Hcr
      ipureintro; simp [Loc.add]; omega

end proof

end Perennial
