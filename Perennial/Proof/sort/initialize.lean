/-
The proof of `sort.initialize'`.
-/
module

public import Perennial.Spec.sort.initialize
public import Perennial.Spec.math.bits.initialize
public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.initialize'.wp_proof
    (wp_bits_initialize : math.bits.initialize'.spec (GF := GF) (hG := hG)) :
    sort.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_bits_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hbits⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
