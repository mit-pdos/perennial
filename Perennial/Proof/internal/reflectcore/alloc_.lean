/-
The proof of `internal.reflectcore.alloc`.
-/
module

public import Perennial.Spec.internal.reflectcore.alloc_

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

theorem internal.reflectcore.alloc.wp_proof :
    internal.reflectcore.alloc.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ t
  wp_start
  wp_auto
  wp_apply (IntoValTyped.wp_alloc (t := T) (zero_val V)) as %q Hq
  iapply HΦ
  iexact Hq

end proof

end Perennial
