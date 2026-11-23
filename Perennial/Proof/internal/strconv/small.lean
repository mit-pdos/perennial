/-
The proof of `internal.strconv.small`.
-/
module

public import Perennial.Spec.internal.strconv.small

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.small.wp_proof : internal.strconv.small.spec (GF := GF) (hG := hG) := by
  intro i h0 h1
  wp_start
  wp_auto
  wp_if_destruct
  · have hi : i.toNat < 10 := by word
    have hl : ((go!"0123456789abcdefghijklmnopqrstuvwxyz" : GoString).length : Int) = 36 := rfl
    rw [hl, if_pos (by word)]
    have h2 : sint.nat (i + W64 1) - sint.nat i = 1 := by word
    have h3 : sint.nat i = i.toNat := by word
    have h4 := internal.strconv.digits_slice ⟨i.toNat, by omega⟩
    simp only at h4
    rw [h2, h3, h4, ← internal.strconv.fmtUint10_lt10 i hi]
    wp_auto
    wp_end
  · have hi1 : 10 ≤ i.toNat := by word
    have hi2 : i.toNat < 100 := by word
    have hl : ((go!"00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899" : GoString).length : Int) = 200 := rfl
    rw [hl, if_pos (by word)]
    have h2 : sint.nat (i * W64 2 + W64 2) - sint.nat (i * W64 2) = 2 := by word
    have h3 : sint.nat (i * W64 2) = 2 * i.toNat := by word
    have h4 := internal.strconv.smalls_slice ⟨i.toNat, by omega⟩
    simp only at h4
    rw [h2, h3, h4, ← internal.strconv.fmtUint10_lt100 i hi1 hi2]
    wp_auto
    wp_end

end proof

end Perennial
