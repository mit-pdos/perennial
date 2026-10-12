/-
Specs for `internal/abi`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.abi

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.abi

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.abi.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.abi :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.abi :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.abi get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.abi }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) kindNames (go.SliceType go.string) as Hk
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) _
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨-, -⟩
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- `abi.NoEscape(p)` returns `p`. -/
theorem wp_NoEscape (p : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.abi }}
      (App (Val (@! NoEscape)) (Val #p))
    {{ RET #p; True }} := by
  wp_start
  wp_end

end wps

end internal.abi

end Perennial
end
