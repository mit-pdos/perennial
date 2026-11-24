/-
The proof of `internal.reflectlite.initialize'`.
-/
module

public import Perennial.Spec.internal.reflectlite.initialize
public import Perennial.Spec.internal.abi.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.internal.reflectcore.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.initialize'.wp_proof
    (wp_abi_initialize : internal.abi.initialize'.spec (GF := GF) (hG := hG))
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_reflectcore_initialize : internal.reflectcore.initialize'.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_reflectcore_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_gomodel_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_abi_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #_⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
