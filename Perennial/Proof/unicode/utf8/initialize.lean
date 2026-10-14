/-
The proof of `unicode.utf8.initialize'`.
-/
module

public import Perennial.Spec.unicode.utf8.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

set_option maxRecDepth 100000 in
theorem unicode.utf8.initialize'.wp_proof :
    unicode.utf8.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray acceptRange 16) acceptRanges
    (go.ArrayType 16 acceptRange.ty) as Hacc
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) first (go.ArrayType 256 go.uint8) as Hfirst
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
