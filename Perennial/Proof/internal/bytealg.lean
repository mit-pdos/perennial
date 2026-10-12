/-
Specs for `internal/bytealg`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.bytealg

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.bytealg

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.bytealg get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

/-- `bytealg.MakeNoZero(n)`, for `0 ≤ n ≤ maxAlloc`: a new slice of `n` bytes (zero in the
model, unspecified in Go: a caller must not read a byte before writing it). -/
theorem wp_MakeNoZero (n : w64) (Hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ maxAlloc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg }}
      (App (Val (@! MakeNoZero)) (Val #n))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* List.replicate (sint.nat n) (W8 0) ∗ ownSliceCap w8 sl (DFrac.own 1) }} := by
  wp_start
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  have Hmax : sint.Z (W64 maxAlloc) = maxAlloc := by unfold maxAlloc; word
  rw [decide_eq_false (show ¬ sint.Z (W64 maxAlloc) < sint.Z n by rw [Hmax]; omega)]
  wp_auto
  wp_apply wp_new_cap with %cap %Hcap
  wp_apply wp_slice_make3 (V := w8) n cap ⟨Hn.1, Hcap⟩ with %sl ⟨Hsl, Hsl_cap, -⟩
  iapply HΦ
  iframe

end wps

end internal.bytealg

end Perennial
end
