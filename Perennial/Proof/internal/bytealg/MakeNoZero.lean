/-
The proof of `internal.bytealg.MakeNoZero`, translated from its Go model
(`goose/model/overlay/internal/bytealg/bytealg.go`).
-/
module

public import Perennial.Spec.internal.bytealg.MakeNoZero
public import Perennial.Spec.internal.gomodel.ChooseUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

set_option maxHeartbeats 2000000 in
theorem internal.bytealg.MakeNoZero.wp_proof
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  wp_auto
  wp_apply wp_ChooseUint64 as %x -
  try wp_auto
  wp_join iprop(∃ c : w64, c_ptr ↦ c ∗ ⌜sint.Z n ≤ sint.Z c⌝) with [c] as ⟨%c, c, %Hc⟩
  all_goals done

end proof

end Perennial
