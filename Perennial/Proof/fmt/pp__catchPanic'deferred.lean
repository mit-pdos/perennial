/-
The proof of `fmt.(*pp).catchPanic (deferred)`.
-/
module

public import Perennial.Spec.fmt.pp__catchPanic'deferred

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.catchPanic'deferred.wp_proof : fmt.pp.catchPanic'deferred.spec (GF := GF) (hG := hG) :=
    fun p pnc arg verb method => by
  wp_start as Hpnc
  wp_auto
  wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
  iapply HΦ
  iframe

end proof

end Perennial
