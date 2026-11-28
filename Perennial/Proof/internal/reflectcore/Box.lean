/-
The proof of `internal.reflectcore.Box`.
-/
module

public import Perennial.Spec.internal.reflectcore.Box
public import Perennial.Spec.internal.reflectcore.box_

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

theorem internal.reflectcore.Box.wp_proof
    (wp_box : internal.reflectcore.box.spec (GF := GF) (hG := hG)) :
    internal.reflectcore.Box.spec (GF := GF) (hG := hG) := fun x hT => by
  wp_start
  wp_apply wp_FuncResolveAt go.Shape.self _ _ _ _ rfl
  rw [show (go!"internal/reflectcore.box" : GoString) = box from rfl]
  wp_apply wp_box x hT as %q Hq
  iapply HΦ
  iexact Hq

end proof

end Perennial
