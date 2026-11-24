/-
The proof of `sync.poolModelAt`, a primitive stub (`TrustedCode/sync.lean`): the identity.
-/
module

public import Perennial.Spec.sync.poolModelAt

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

theorem sync.poolModelAt.wp_proof :
    sync.poolModelAt.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as _
  iapply HΦ
  itrivial

end proof

end Perennial
