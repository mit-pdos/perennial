/-
The proof of `sync.(*RWMutex).RLocker`.
-/
module

public import Perennial.Spec.sync.RWMutex__RLocker

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.RWMutex.RLocker.wp_proof :
    sync.RWMutex.RLocker.spec (GF := GF) (hG := hG) := by
  intro rw
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
