/-
Port of `new/proof/io.v`: package initialization of `io`.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.errors
import Perennial.Code.io
import Perennial.GeneratedProof.io

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace io

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.io get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.io }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := interface.t) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) blackHolePool sync.Pool.ty as _
  repeat (wp_apply wp_GlobalAlloc (V := interface.t) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := interface.t) Discard Writer.ty as _
  repeat (wp_apply wp_GlobalAlloc (V := interface.t) _ go.error as _)
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (wp_apply errors.wp_New as %_ _)
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  wp_apply errors.wp_New as %_ _
  iframe Hown
  is_pkg_init_finish

end wps

end io

end Perennial
end
