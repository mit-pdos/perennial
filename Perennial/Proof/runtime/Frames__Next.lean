/-
The proof of `runtime.Frames.Next` (its Go model, `goose/model/overlay/runtime`).
-/
module

public import Perennial.Spec.runtime.Frames__Next
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64
public import Perennial.Spec.internal.gomodel.ChooseString

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

theorem runtime.Frames.Next.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_ChooseString : internal.gomodel.ChooseString.spec (GF := GF) (hG := hG)) :
    runtime.Frames.Next.spec (GF := GF) (hG := hG) := fun f => by
  wp_start as Hf
  unfold runtime.ownFrames
  icases Hf with ⟨%v, Hf⟩
  wp_auto
  wp_apply wp_ChooseUint64 as %pc -
  wp_apply wp_Choose as %c -
  rcases c with _ | _
  all_goals
    try (wp_auto; wp_alloc fp as Hfp)
    wp_auto
    wp_apply wp_ChooseString as %fn -
    wp_apply wp_ChooseString as %file -
    wp_apply wp_ChooseUint64 as %line -
    wp_apply wp_ChooseUint64 as %sl -
    wp_apply wp_ChooseUint64 as %entry -
    wp_apply wp_Choose as %m -
    iapply HΦ
    iexists _
    iexact Hf

end proof

end Perennial
