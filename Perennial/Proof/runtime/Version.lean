/-
The proof of `runtime.Version`.
-/
module

public import Perennial.Spec.runtime.Version

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.Version.wp_proof :
    runtime.Version.spec (GF := GF) (hG := hG) := by
  wp_start as ⟨#Hinit, -⟩
  iapply runtime.isInit_access $$ Hinit
  iintro ⟨%v, #Hv⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
