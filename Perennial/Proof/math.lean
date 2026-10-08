/-
Package initialization of `math`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.math
import Perennial.GeneratedProof.math

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math :=
  build_get_is_pkg_init_wf

/-- The initializer of `math` calls the package's (unmodeled) `init` function
`_'init`, so this is not provable. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.math get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.math }} := by
  -- Unprovable: `useFMA'init`, `_sin'init`, ... are opaque (axioms in Perennial/Code/math.lean).
  sorry

end wps

end math

end Perennial
end
