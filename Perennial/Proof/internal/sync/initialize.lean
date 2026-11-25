/-
The proof of `internal.sync.initialize'`.
-/
module

public import Perennial.Spec.internal.sync.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.sync.atomic.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

theorem internal.sync.initialize'.wp_proof
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_atomic_initialize : sync.atomic.initialize'.spec (GF := GF) (hG := hG)) :
    internal.sync.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_gomodel_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hgomodel⟩
  wp_apply wp_atomic_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
