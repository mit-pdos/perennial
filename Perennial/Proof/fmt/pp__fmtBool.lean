/-
The proof of `fmt.(*pp).fmtBool`.
-/
module

public import Perennial.Spec.fmt.pp__fmtBool
public import Perennial.Spec.fmt.fmt__fmtBoolean

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.fmtBool.wp_proof (wp_fmtBoolean : fmt.fmt.fmtBoolean.spec (GF := GF) (hG := hG)) :
    fmt.pp.fmtBool.spec (GF := GF) (hG := hG) := fun p x bs wid prec v => by
  wp_start as Hp
  unfold isPrinterA
  icases Hp with ⟨Hb, Hf, Hrest⟩
  wp_auto
  wp_apply wp_fmtBoolean _ _ noFlags wid prec bs v (Or.inl rfl) $$ [Hf Hb] as ⟨Hf, Hb⟩
  · iframe
  iapply HΦ
  iframe

end proof

end Perennial
