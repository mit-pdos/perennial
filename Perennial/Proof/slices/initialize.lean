/-
The proof of `slices.initialize'`.
-/
module

public import Perennial.Spec.slices.initialize
public import Perennial.Spec.math.bits.initialize
public import Perennial.Spec.cmp.initialize
public import Perennial.Proof.slices.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.initialize'.wp_proof
    (wp_bits_initialize : math.bits.initialize'.spec (GF := GF) (hG := hG))
    (wp_cmp_initialize : cmp.initialize'.spec (GF := GF) (hG := hG)) :
    slices.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_bits_initialize _ Hinit.2.2.1 $$ Hown with ⟨Hown, #Hbits⟩
  wp_apply wp_cmp_initialize _ Hinit.2.1 $$ Hown with ⟨Hown, #Hcmp⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
