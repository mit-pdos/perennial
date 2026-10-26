/-
The proof of `strings.Fields`.
-/
module

public import Perennial.Spec.strings.Fields

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- FIXME: this is wrong (unsound) for strings with non-ASCII
runes. Simplest solution might be to add a precondition for the string to be
all ASCII. -/
axiom strings.Fields.wp_proof : strings.Fields.spec (GF := GF) (hG := hG)

/-! Unit tests of the axiom. -/

example :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! strings.Fields)) (Val #(go!"  hello\tthere\ngeneral\rkenobi ")))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* [go!"hello", go!"there", go!"general", go!"kenobi"] ∗
        ownSliceCap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto strings.Fields.wp_proof with %sl ⟨Hsl, Hcap⟩
  have h : strings.splitFields go!"  hello\tthere\ngeneral\rkenobi " =
      [go!"hello", go!"there", go!"general", go!"kenobi"] := by decide
  rw [h]
  iapply HΦ
  iframe

example :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! strings.Fields)) (Val #(go!"hello world")))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* [go!"hello", go!"world"] ∗
        ownSliceCap w8 sl (DFrac.own 1) }} := by
  iintro %Φ #Hinit HΦ
  wp_apply +noauto strings.Fields.wp_proof go!"hello world" with %sl ⟨Hsl, Hcap⟩
  have h : strings.splitFields go!"hello world" = [go!"hello", go!"world"] := by decide
  rw [h]
  iapply HΦ
  iframe

end proof

end Perennial
