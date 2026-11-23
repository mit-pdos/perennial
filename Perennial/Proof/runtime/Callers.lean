/-
The proof of `runtime.Callers`.
-/
module

public import Perennial.Spec.runtime.Callers
public import Perennial.Spec.runtime.callers_

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.Callers.wp_proof
    (wp_callers : runtime.callers.spec (GF := GF) (hG := hG)) :
    runtime.Callers.spec (GF := GF) (hG := hG) := fun skip s xs => by
  wp_start as Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iexists xs
    iframe
    ipureintro
    simp [show sint.Z (W64 0) = 0 from rfl, show sint.nat (W64 0) = 0 from rfl]
  · wp_apply wp_callers $$ Hs as %n Hn
    iapply HΦ $$ Hn

end proof

end Perennial
