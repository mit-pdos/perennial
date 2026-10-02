/-
Port of `new/proof/slices_proof/slices_init.v`: package initialization of
`slices`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.slices
import Perennial.GeneratedProof.slices
import Perennial.Proof.math.bits

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.slices :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.slices :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.slices get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.slices }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply math.bits.wp_initialize' _ Hinit.2.1 $$ Hown with ⟨Hown, #Hbits⟩
  iframe Hown
  is_pkg_init_finish

end proof

end slices

end Perennial
end
