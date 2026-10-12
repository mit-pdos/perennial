/-
Package initialization of `log` and `log.Printf`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.log
public import Perennial.GeneratedProof.log
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.log :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.log :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.log get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.log }} := by
  -- Unprovable: `std'init` and `bufferPool'init` are opaque (axioms in Perennial/Code/log.lean).
  sorry

/-- `log.Printf(format, args...)` returns; the output is not modelled. The model
(`TrustedCode/log.lean`) does nothing, while Go formats the arguments as `fmt.Sprintf` does,
calling the `Error()`/`String()` methods of arguments that have them: so the arguments must be of
predeclared basic types (`fmt.ArgsWf`), for which Go calls no method. -/
theorem wp_Printf (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (Hxs : fmt.ArgsWf xs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (App (Val (@! Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  wp_start as Hsl
  wp_end

end wps

end log

end Perennial
end
