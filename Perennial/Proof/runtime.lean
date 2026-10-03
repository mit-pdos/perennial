/-
Port of `new/proof/runtime.v`: package initialization of `runtime` and
`runtime.Gosched`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.runtime
import Perennial.GeneratedProof.runtime
import Perennial.Proof.internal.runtime.atomic
import Perennial.Proof.internal.runtime.sys

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace runtime

section defns
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.runtime :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.runtime :=
  build_get_is_pkg_init_wf

theorem wp_Gosched :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.runtime ∗ True }}
      (App (Val (@! Gosched)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end defns

end runtime

end Perennial
end
