/-
Port of `new/proof/log.v`: package initialization of `log` and `log.Printf`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.log
import Perennial.GeneratedProof.log

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.log :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.log :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.log get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.log }} := by
  sorry -- Rocq: Admitted

theorem wp_Printf (msg : go_string) (arg : slice.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.log }}
      (App (App (Val (@! Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

end log

end Perennial
end
