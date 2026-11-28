/-
The proof of `internal.reflectcore.ConvertAt`.
-/
module

public import Perennial.Spec.internal.reflectcore.ConvertAt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [HasExt reflectExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.ConvertAt.wp_proof :
    internal.reflectcore.ConvertAt.spec (GF := GF) (hG := hG) := by
  constructor
  · intro t u uu _ X Y x y _ l hu hn het heu
    wp_start
    wp_apply wp_ConvertAt hu hn x y l het heu
    iapply HΦ
    itrivial
  · intro t u uu _ v l hu himpl het heu
    wp_start
    wp_apply wp_ConvertAt_interface hu himpl v l het heu
    iapply HΦ
    itrivial

end proof

end Perennial
