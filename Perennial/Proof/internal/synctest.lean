/-
Port of `new/proof/internal/synctest.v`: specs for `internal/synctest`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.GeneratedProof.internal.synctest

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.synctest

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.synctest :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.synctest :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.synctest get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.synctest }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- `synctest.Run` is not supported by Perennial; it changes the semantics of go
programs because it messes with runtime state (i.e. it creates a new bubble). -/
theorem wp_Run (v : func.t) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.synctest ∗ False }}
      (App (Val (@! Run)) (Val #v))
    {{ RET #(); True }} := by
  wp_start as ⟨⟩

/-- `synctest.IsInBubble` always returns false since Perennial doesn't permit
`synctest.Run`. -/
theorem wp_IsInBubble :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.synctest }}
      (App (Val (@! IsInBubble)) (Val #()))
    {{ RET #false; True }} := by
  wp_start
  wp_end

end wps

end internal.synctest

end Perennial
end
