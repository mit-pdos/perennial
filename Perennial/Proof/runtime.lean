/-
Package initialization of `runtime` and
`runtime.Gosched`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.runtime
public import Perennial.GeneratedProof.runtime
public import Perennial.Proof.internal.runtime.atomic
public import Perennial.Proof.internal.runtime.sys

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace runtime

section defns
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.runtime :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.runtime :=
  build_get_is_pkg_init_wf

theorem wp_Gosched :
    {{ isPkgInit (PROP := IProp GF) pkg_id.runtime ∗ True }}
      (App (Val (@! Gosched)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

end defns

end runtime

end Perennial
end
