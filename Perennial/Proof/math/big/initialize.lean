/-
The proof of `math/big.initialize'`.
-/
module

public import Perennial.Spec.math.big.initialize
public import Perennial.Spec.fmt.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.big.Assumptions]

theorem math.big.initialize'.wp_proof
    (wp_fmt_initialize : fmt.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    math.big.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoArray w8 _) _ (go.ArrayType _ go.uint8) as _
    | wp_apply wp_GlobalAlloc (V := GoArray w64 _) _ (go.ArrayType _ go.uint64) as _
    | wp_apply wp_GlobalAlloc (V := Loc) _ (go.PointerType _) as _
    | wp_apply wp_GlobalAlloc (V := GoSlice) _ nat.ty as _
    | wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _
    | wp_apply wp_GlobalAlloc (V := w64) _ go.int as _)
  wp_apply wp_errors_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  wp_apply wp_fmt_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hfmt⟩
  -- the variables, in Go's initialization order; `hasADX`'s trusted initializer does nothing
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (wp_apply wp_slice_literal (V := w64) [_]
       isplitr
       · ipureintro; rfl
       iintro %_ ⟨_, _⟩)
    | wp_call
    | wp_auto)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
