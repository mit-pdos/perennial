/-
The proof of `internal.bytealg.initialize'`.
-/
module

public import Perennial.Spec.internal.bytealg.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.internal.gomodel.Choose

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem internal.bytealg.initialize'.wp_proof
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG)) :
    internal.bytealg.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := w64) _ go.int as HMaxLen
  wp_apply wp_gomodel_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hgomodel⟩
  -- `init.0` (its Go model): `MaxLen` is 63 or 31, as `gomodel.Choose()` says
  wp_func_call
  wp_call
  iunfold MaxLen at HMaxLen
  wp_apply wp_Choose as %c -
  iapply wp_fupd
  wp_if_destruct <;>
  · unfold MaxLen
    try wp_auto
    ipersist HMaxLen
    iframe Hown
    is_pkg_init_finish
    isplitr
    · ipureintro; simp
    imodintro
    unfold internal.bytealg.isInit MaxLen
    iexists _
    iframe HMaxLen
    ipureintro
    simp

end proof

end Perennial
