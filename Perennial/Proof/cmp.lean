/-
Port of `new/proof/cmp.v`: package initialization for `cmp`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.cmp
import Perennial.GeneratedProof.cmp

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace cmp

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.cmp :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.cmp :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.cmp get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.cmp }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end wps

end cmp

end Perennial
end
