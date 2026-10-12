/-
The proof of `errors.New`.
-/
module

public import Perennial.Spec.errors.New

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

/-- Proven first because it is used during package initialization (to create
global error variables). -/
theorem errors.New.wp_proof :
    errors.New.spec (GF := GF) (hG := hG) := by
  intro msg
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  isplitl []
  · ipureintro; exact ⟨_, x, rfl, rfl⟩
  imodintro
  iintro %Φ HΦ
  dsimp only
  rw [method_unfold]
  wp_auto
  iexact HΦ

end proof

end Perennial
