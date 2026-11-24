/-
The proof of `reflect.Kind.String`.
-/
module

public import Perennial.Spec.reflect.Kind__String

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.Kind.String.wp_proof :
    reflect.Kind.String.spec (GF := GF) (hG := hG) := fun k name hk => by
  have hlt : uint.nat k < 27 := by
    have := (List.getElem?_eq_some_iff.mp hk).1
    simpa [reflect.kindNamesVal] using this
  wp_start
  ihave ⟨%sl, #Hg, #Hsl⟩ := reflect.isInit_access $$ Hpkg
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have h27 : (reflect.kindNamesVal).length = 27 := rfl
  have hc : uint.Z k < uint.Z sl.len := by
    obtain ⟨h1, h2⟩ := Hlen
    rw [h27] at h1
    simp only [uint.nat, sint.nat, uint.Z, sint.Z] at *
    word
  wp_auto
  rw [decide_eq_true hc]
  wp_auto
  have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
    obtain ⟨h1, h2⟩ := Hlen
    rw [h27] at h1
    simp only [uint.nat, sint.nat, uint.Z, sint.Z] at *
    word
  have hidx : (reflect.kindNamesVal)[(sint.Z k).toNat]? = some name := by
    rw [← hk]; congr 1
    simp only [uint.nat, sint.nat, uint.Z, sint.Z] at *
    word
  rw [ite_eq_left hb]
  wp_apply wp_load_slice_index _ _ _ _ name hb.1 $$ [$Hsl] as -
  · ipureintro; exact hidx
  iapply HΦ
  itrivial

end proof

end Perennial
