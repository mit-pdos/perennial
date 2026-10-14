/-
The proof of `bytes.initialize'`.
-/
module

public import Perennial.Spec.bytes.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.initialize'.wp_proof
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    bytes.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) as _
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (wp_apply wp_New as %_ _)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
