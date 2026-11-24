/-
The proof of `internal.reflectlite.flag.kind`.
-/
module

public import Perennial.Spec.internal.reflectlite.flag__kind

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

theorem internal.reflectlite.flag.kind.wp_proof :
    internal.reflectlite.flag.kind.spec (GF := GF) (hG := hG) := fun f => by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
