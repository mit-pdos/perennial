/-
The proof of `internal.strconv.initialize'`.
-/
module

public import Perennial.Spec.internal.strconv.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem internal.strconv.initialize'.wp_proof :
    internal.strconv.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := Bool) _ go.bool as _
    | wp_apply wp_GlobalAlloc (V := GoSlice) _ (go.SliceType _) as _
    | wp_apply wp_GlobalAlloc (V := internal.strconv.floatInfo) _ internal.strconv.floatInfo.ty as _
    | wp_apply wp_GlobalAlloc (V := GoArray w64 _) _ (go.ArrayType _ go.uint64) as _
    | wp_apply wp_GlobalAlloc (V := GoArray (GoArray w64 _) _) _
        (go.ArrayType _ (go.ArrayType _ go.uint64)) as _)
  -- the variables' initializers: `optimize`, then the constant tables
  repeat (first
    | (wp_apply wp_slice_literal (V := w64) (t := go.int) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | (wp_apply wp_slice_literal (V := w64) (t := go.float64) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | (wp_apply wp_slice_literal (V := w32) (t := go.float32) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | (wp_apply wp_slice_literal (V := internal.strconv.leftCheat) (t := internal.strconv.leftCheat.ty) _
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | wp_auto)
  -- pow10Tab: its trusted initializer does nothing
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
