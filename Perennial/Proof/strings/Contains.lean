/-
The proof of `strings.Contains`.
-/
module

public import Perennial.Spec.strings.Contains
public import Perennial.Spec.strings.Index

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- `substr` occurs in `s` exactly when it is a prefix of some suffix `s.drop j`. -/
theorem strings.infix_iff_exists_prefix_drop (s substr : List w8) :
    substr <:+: s ↔ ∃ j, substr <+: s.drop j := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a.length, ⟨b, by simp⟩⟩
  · rintro ⟨j, t, ht⟩
    exact ⟨s.take j, t, by rw [List.append_assoc, ht, List.take_append_drop]⟩

/-- `index s substr` is nonnegative exactly when `substr` occurs in `s`. -/
theorem strings.index_nonneg_iff (s substr : List w8) :
    0 ≤ internal.bytealg.index s substr ↔ substr <:+: s := by
  rw [strings.infix_iff_exists_prefix_drop]
  rcases internal.bytealg.index_cases s substr with ⟨i, hi, hp, -⟩ | ⟨hi, hn⟩
  · rw [hi]; exact ⟨fun _ => ⟨i, hp⟩, fun _ => by omega⟩
  · rw [hi]; exact ⟨fun h => by omega, fun ⟨j, hj⟩ => absurd hj (hn j)⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Contains.wp_proof
    (wp_Index : strings.Index.spec (GF := GF) (hG := hG)) :
    strings.Contains.spec (GF := GF) (hG := hG) := by
  intro s substr
  wp_start as #Hinit
  wp_auto
  wp_apply wp_Index as %Hl
  have hb := internal.bytealg.index_bounds s substr
  have heq : sint.Z (W64 0) ≤ sint.Z (W64 (internal.bytealg.index s substr)) ↔ substr <:+: s := by
    rw [← strings.index_nonneg_iff]
    by_cases h : substr = []
    · subst h
      rw [internal.bytealg.index_eq_of s [] 0 (by simp) (by simp)]
      simp
    · have hs := Hl h
      have hlt : internal.bytealg.index s substr < 2 ^ 63 := by omega
      rw [show sint.Z (W64 (internal.bytealg.index s substr)) = internal.bytealg.index s substr by
        word]
      simp
  rw [decide_eq_decide.mpr heq]
  iapply HΦ
  itrivial

end proof

end Perennial
