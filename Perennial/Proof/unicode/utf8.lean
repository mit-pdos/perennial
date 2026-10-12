/-
Package initialization of `unicode/utf8`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.unicode.utf8

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace unicode.utf8

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.unicode.utf8 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.unicode.utf8 :=
  build_get_is_pkg_init_wf

set_option maxRecDepth 100000 in
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.unicode.utf8 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }} := by
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

end wps

end unicode.utf8

end Perennial
end
