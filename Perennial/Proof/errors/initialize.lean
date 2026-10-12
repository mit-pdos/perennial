/-
The proof of `errors.initialize'`.
-/
module

public import Perennial.Spec.errors.initialize
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

/-- Uses the unproved `wp_errorType_init` (`Base.lean`). -/
theorem errors.initialize'.wp_proof
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    errors.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupported go.error as _
  wp_apply wp_New as %_ _
  wp_apply wp_errorType_init
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
