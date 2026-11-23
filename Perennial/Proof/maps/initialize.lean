/-
The proof of `maps.initialize'`.
-/
module

public import Perennial.Spec.maps.initialize
public import Perennial.Spec.iter.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

theorem maps.initialize'.wp_proof
    (wp_iter_initialize : iter.initialize'.spec (GF := GF) (hG := hG)) :
    maps.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_iter_initialize _ Hinit.2.1 $$ Hown with ⟨Hown, #Hiter⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
