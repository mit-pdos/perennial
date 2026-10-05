/-
Port of `new/proof/internal/race.v`: package initialization of `internal/race`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.internal.race
import Perennial.GeneratedProof.internal.race

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.race

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.race.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.race :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.race :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.race get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.race }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end init

end internal.race

end Perennial
end
