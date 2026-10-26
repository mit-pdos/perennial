/-
The proof of `math.initialize'`.
-/
module

public import Perennial.Spec.math.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

theorem math.initialize'.wp_proof :
    math.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoArray w64 _) _ (go.ArrayType _ _) as _)
  -- useFMA: its trusted initializer does nothing
  wp_call
  -- the tables
  wp_auto
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
