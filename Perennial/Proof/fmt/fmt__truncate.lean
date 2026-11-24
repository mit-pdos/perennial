/-
The proof of `fmt.(*fmt).truncate`.
-/
module

public import Perennial.Spec.fmt.fmt__truncate

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.fmt.truncate.wp_proof : fmt.fmt.truncate.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec sl hF => by
  wp_start as Hf
  unfold fmt.fmtOwn
  icases Hf with ⟨Hb, HF, Hw, Hp⟩
  wp_auto
  rw [hF]
  wp_auto
  iapply HΦ
  iframe

end proof

end Perennial
