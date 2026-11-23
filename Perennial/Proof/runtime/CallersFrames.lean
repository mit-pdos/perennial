/-
The proof of `runtime.CallersFrames`.
-/
module

public import Perennial.Spec.runtime.CallersFrames

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

theorem runtime.CallersFrames.wp_proof :
    runtime.CallersFrames.spec (GF := GF) (hG := hG) := fun s => by
  wp_start
  wp_auto
  iapply HΦ
  unfold runtime.ownFrames
  iexists _
  iexact «$r0»

end proof

end Perennial
