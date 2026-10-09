/-
Package initialization of `fmt`, `fmt.Errorf` and `fmt.Printf`.
-/
module

public import Perennial.Proof.io
public import Perennial.Code.fmt
public import Perennial.GeneratedProof.fmt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace fmt

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.fmt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.fmt :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.fmt get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.fmt }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) ssFree sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoSlice) space _ as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) ppFree sync.Pool.ty as _
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_slice_literal (V := GoArray w16 2)
    [array.mk 2 [W16 9, W16 13], array.mk 2 [W16 32, W16 32], array.mk 2 [W16 133, W16 133], array.mk 2 [W16 160, W16 160], array.mk 2 [W16 5760, W16 5760], array.mk 2 [W16 8192, W16 8202], array.mk 2 [W16 8232, W16 8233], array.mk 2 [W16 8239, W16 8239], array.mk 2 [W16 8287, W16 8287], array.mk 2 [W16 12288, W16 12288]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  repeat (first
    | (wp_apply errors.wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  iframe Hown
  is_pkg_init_finish

/-- This is unsound: really need to know that all of the args are
safe to convert into string. The error's `Error()` returns some string (a `*fmt.wrapError`
or `*errors.errorString`). -/
theorem wp_Errorf (format : GoString) (args_sl : GoSlice) (args : List GoAny) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  -- Unprovable: `fmt.Errorf` has no translated body (no `FuncUnfold` in `fmt.Assumptions`).
  sorry

/-- `fmt.Printf(format, args...)` returns; the output is not modelled, nor the results. -/
theorem wp_Printf (format : GoString) (args_sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (App (Val (@! Printf)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); True }} := by
  wp_start
  iapply HΦ
  itrivial

end wps

end fmt

end Perennial
end
