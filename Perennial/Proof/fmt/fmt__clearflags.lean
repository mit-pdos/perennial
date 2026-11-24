/-
The proof of `fmt.(*fmt).clearflags`.
-/
module

public import Perennial.Spec.fmt.fmt__clearflags

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

theorem fmt.fmt.clearflags.wp_proof : fmt.fmt.clearflags.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec => by
  wp_start as Hf
  unfold fmt.fmtOwn
  icases Hf with ⟨Hb, HF, Hw, Hp⟩
  wp_auto
  rw [show _root_.Perennial.zero_val fmt.fmtFlags = noFlags from rfl]
  iapply HΦ
  iframe

end proof

end Perennial
