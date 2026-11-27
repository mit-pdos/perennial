/-
The proof of `math.initialize'`.
-/
module

public import Perennial.Spec.math.initialize
public import Perennial.Spec.internal.gomodel.initialize

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

theorem math.initialize'.wp_proof
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG)) :
    math.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (wp_apply wp_GlobalAlloc (V := GoArray w64 _) _ (go.ArrayType _ _) as _)
  -- the Go model's `internal/gomodel` (goose/model/overlay/math)
  wp_apply wp_gomodel_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hgm⟩
  -- useFMA: its trusted initializer does nothing
  wp_call
  -- the tables
  wp_auto
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
