/-
The proof of `internal.reflectcore.tokOf`.
-/
module

public import Perennial.Spec.internal.reflectcore.tokOf_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.tokOf.wp_proof :
    internal.reflectcore.tokOf.spec (GF := GF) (hG := hG) := fun T x => by
  unfold go.tok
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
