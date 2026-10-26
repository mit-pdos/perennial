/-
The proof of `internal.synctest.IsInBubble`.
-/
module

public import Perennial.Spec.internal.synctest.IsInBubble

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

theorem internal.synctest.IsInBubble.wp_proof :
    internal.synctest.IsInBubble.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_end

end proof

end Perennial
