/-
Port of `new/proof/math.v`: package initialization of `math`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.math
import Perennial.GeneratedProof.math

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.math :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math :=
  build_get_is_pkg_init_wf

/-- The initializer of `math` calls the package's (unmodeled) `init` function
`_'init`, so this is not provable. -/
theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.math get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.math }} := by
  sorry -- Rocq: Admitted

end wps

end math

end Perennial
end
