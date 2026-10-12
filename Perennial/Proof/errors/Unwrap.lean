/-
The proof of `errors.Unwrap`.
-/
module

public import Perennial.Spec.errors.Unwrap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

theorem errors.Unwrap.wp_proof :
    errors.Unwrap.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hunwrap
  wp_auto
  cases err with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok ii =>
    dsimp only
    cases Hhas_unwrap : go.typeSetContains ii.ty
      (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])])
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_end
    · simp only [↓reduceIte]
      wp_auto
      have hu : underlying (go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])]) =
          go.InterfaceType [go.MethodElem go!"Unwrap" (go.Signature [] false [go.error])] :=
        go.is_underlying
      simp only [go.typeSetContains, hu, go.typeSetElemsContains, go.typeSetElemContains,
        List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at Hhas_unwrap
      simp only [isUnwrappable, Hhas_unwrap, ↓reduceIte]
      wp_apply Hunwrap as %_ _
      wp_end

end proof

end Perennial
