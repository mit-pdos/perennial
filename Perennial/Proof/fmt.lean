/-
Port of `new/proof/fmt.v`: package initialization of `fmt` and `fmt.Errorf`.
-/
import Perennial.Proof.io
import Perennial.Code.fmt
import Perennial.GeneratedProof.fmt

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.fmt :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.fmt :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.fmt get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.fmt }} := by
  -- Unprovable: `errBool'init`, `ppFree'init`, ... are opaque (axioms in Perennial/Code/fmt.lean).
  sorry -- Rocq: Admitted

/-- This is unsound (Rocq comment): really need to know that all of the args are
safe to convert into string. -/
theorem wp_Errorf (format : go_string) (args_sl : slice.t) (args : List any.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : interface.t_ok), RET #(interface.ok err); True }} := by
  -- Unprovable: `fmt.Errorf` has no translated body (no `FuncUnfold` in `fmt.Assumptions`).
  sorry -- Rocq: Admitted

end wps

end fmt

end Perennial
end
