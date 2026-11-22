/-
The proof of `reflect.initialize'`.
-/
module

public import Perennial.Spec.reflect.initialize
public import Perennial.Spec.internal.abi.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.initialize'.wp_proof
    (wp_abi_initialize : internal.abi.initialize'.spec (GF := GF) (hG := hG)) :
    reflect.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) kindNames (go.GoType.SliceType go.string) as Hk
  wp_apply wp_GlobalAlloc (V := w64) floatRegSize go.uintptr as Hfs
  wp_apply wp_GlobalAlloc (V := w64) floatArgRegs go.int as Hfa
  wp_apply wp_GlobalAlloc (V := w64) intArgRegs go.int as Hia
  wp_apply wp_abi_initialize _ Hinit.2.1 $$ Hown with ⟨Hown, #Habi⟩
  -- stringType, bytesType, uint8Type: their trusted initializers do nothing
  wp_call
  -- kindNames
  wp_apply wp_slice_literal (V := GoString) (t := go.string) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨_, _⟩
  wp_auto
  wp_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
