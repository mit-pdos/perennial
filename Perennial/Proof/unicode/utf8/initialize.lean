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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem unicode.utf8.initialize'.wp_proof :
    unicode.utf8.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoArray w8 _) _ (go.ArrayType _ go.uint8) as _
    | wp_apply wp_GlobalAlloc (V := GoArray unicode.utf8.acceptRange _) _
        (go.ArrayType _ unicode.utf8.acceptRange.ty) as _)
  -- the tables `first` and `acceptRanges` (their literals, by the steps above)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
