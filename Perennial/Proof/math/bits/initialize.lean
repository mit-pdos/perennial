/-
The proof of `math.bits.initialize'`.
-/
module

public import Perennial.Spec.math.bits.initialize
public import Perennial.Spec.«unsafe».initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem math.bits.initialize'.wp_proof
    (wp_unsafe_initialize : «unsafe».initialize'.spec (GF := GF) (hG := hG)) :
    math.bits.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) divideError go.error with _
  wp_apply wp_GlobalAlloc (V := GoInterface) overflowError go.error with _
  wp_apply wp_GlobalAlloc (V := GoArray w8 64) deBruijn64tab (go.ArrayType 64 go.byte) with H1
  wp_apply wp_GlobalAlloc (V := GoArray w8 32) deBruijn32tab (go.ArrayType 32 go.byte) with H2
  wp_apply wp_unsafe_initialize _ Hinit.2.1 $$ Hown with ⟨Hown, #Hunsafe⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
