/-
The proof of `errors.AsType`.
-/
module

public import Perennial.Spec.errors.AsType
public import Perennial.Spec.errors.asType_

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

theorem errors.AsType.wp_proof
    (wp_asType : errors.asType.spec (GF := GF) (hG := hG)) :
    errors.AsType.spec (GF := GF) (hG := hG) := by
  intro S err T' _ _ T _
  wp_start as H
  iNamed H
  wp_auto
  cases err with
  | nil =>
    wp_auto
    wp_end
  | ok ii =>
    wp_auto
    wp_apply wp_asType S (interface.ok ii) pe_ptr (zero_val Loc) $$ [pe] as %e %found %pe' _
    · iframe; iframe #; iframe %; ileft; ipureintro; rfl
    wp_end

end proof

end Perennial
