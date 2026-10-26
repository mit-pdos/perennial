/-
The proof of `fmt.initialize'`.
-/
module

public import Perennial.Spec.fmt.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.io.initialize
public import Perennial.Spec.errors.initialize
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    fmt.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) ssFree sync.Pool.ty as _
  wp_apply wp_GlobalAlloc (V := GoSlice) space _ as _
  wp_apply wp_GlobalAlloc (V := sync.Pool) ppFree sync.Pool.ty as _
  wp_apply wp_sync_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_slice_literal (V := GoArray w16 2)
    [array.mk 2 [W16 9, W16 13], array.mk 2 [W16 32, W16 32], array.mk 2 [W16 133, W16 133], array.mk 2 [W16 160, W16 160], array.mk 2 [W16 5760, W16 5760], array.mk 2 [W16 8192, W16 8202], array.mk 2 [W16 8232, W16 8233], array.mk 2 [W16 8239, W16 8239], array.mk 2 [W16 8287, W16 8287], array.mk 2 [W16 12288, W16 12288]]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hcap⟩
  repeat (first
    | (wp_apply wp_New as %_ _)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
