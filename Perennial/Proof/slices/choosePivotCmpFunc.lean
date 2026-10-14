/-
The proof of `slices.choosePivotCmpFunc`.
-/
module

public import Perennial.Spec.slices.choosePivotCmpFunc
public import Perennial.Spec.slices.medianCmpFunc
public import Perennial.Spec.slices.medianAdjacentCmpFunc
public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.choosePivotCmpFunc.wp_proof
    (wp_medianCmpFunc : slices.medianCmpFunc.spec (GF := GF) (hG := hG))
    (wp_medianAdjacentCmpFunc : slices.medianAdjacentCmpFunc.spec (GF := GF) (hG := hG)) :
    slices.choosePivotCmpFunc.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ data a b cmp_code xs
  wp_start as H
  iNamed H
  wp_auto
  have Hl : sint.Z (b - a) = sint.Z b - sint.Z a := by word
  have Hd := sint_sdiv4 (b - a) (by omega)
  rw [Hl] at Hd
  generalize BitVec.sdiv (b - a) (W64 4) = d at Hd ⊢
  simp only [W64_1, W64_2, W64_3]
  obtain ⟨Hi, Hj, Hk⟩ := part_choosePivot_idx a b d xs.length Hab_bound Hd
  wp_if_destruct
  · have h8 : 8 ≤ sint.Z b - sint.Z a := by rw [← Hl]; exact Hif
    wp_if_destruct
    · wp_apply wp_medianAdjacentCmpFunc R data (a + d * 1) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %ri %sw1 ⟨Hxs, %Hri, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi]; omega
      wp_apply wp_medianAdjacentCmpFunc R data (a + d * 2) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rj %sw2 ⟨Hxs, %Hrj, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hj]; omega
      wp_apply wp_medianAdjacentCmpFunc R data (a + d * 3) swaps_ptr cmp_code (DFrac.own 1)
        xs _ $$ [Hxs swaps] with %rk %sw3 ⟨Hxs, %Hrk, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hk]; omega
      rw [Hi] at Hri; rw [Hj] at Hrj; rw [Hk] at Hrk
      wp_apply wp_medianCmpFunc R data ri rj rk swaps_ptr cmp_code (DFrac.own 1) xs _
        $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
    · wp_apply wp_medianCmpFunc R data (a + d * 1) (a + d * 2) (a + d * 3) swaps_ptr
        cmp_code (DFrac.own 1) xs _ $$ [Hxs swaps] with %r %sw4 ⟨Hxs, %Hr, swaps⟩
      · iframe; iframe #; ipureintro; rw [Hi, Hj, Hk]; omega
      have : sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b := by
        rcases Hr with h | h | h <;> subst h <;> omega
      wp_if_destruct <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)
  · have : sint.Z a ≤ sint.Z (a + d * 2) ∧ sint.Z (a + d * 2) < sint.Z b := by
      rw [Hj]; omega
    (try wp_if_destruct) <;> (try wp_if_destruct) <;> ((try simp only [increasingHint, decreasingHint, unknownHint]); iapply HΦ; iframe; ipureintro; exact this)

end proof

end Perennial
