/-
The proof of `internal.reflectcore.Alloc`.
-/
module

public import Perennial.Spec.internal.reflectcore.Alloc
public import Perennial.Spec.internal.reflectcore.alloc_

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

theorem internal.reflectcore.Alloc.wp_proof
    (wp_alloc : internal.reflectcore.alloc.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.Alloc.spec (GF := GF) (hG := hG) := fun v => by
  wp_start
  wp_apply wp_FuncResolveAt (go.Shape.deref go.Shape.self) _ _ _ _ rfl
  rw [show (go!"internal/reflectcore.alloc" : GoString) = alloc from rfl]
  wp_apply wp_alloc _ as %q Hq
  iapply HΦ
  iexact Hq

end proof

end Perennial
