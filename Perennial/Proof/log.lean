/-
Package initialization of `log` and `log.Printf`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.log
public import Perennial.GeneratedProof.log

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

theorem wp_Printf (msg : GoString) (arg : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
      (App (App (Val (@! Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end wps

end log

end Perennial
end
