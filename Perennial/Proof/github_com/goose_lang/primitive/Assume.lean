/-
The proof of `github.com/goose-lang/primitive.Assume`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.Assume

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- For `cond = false`, `Assume` loops forever, proved by Löb induction. -/
theorem github_com.goose_lang.primitive.Assume.wp_proof :
    github_com.goose_lang.primitive.Assume.spec (GF := GF) (hG := hG) := by
  intro cond
  wp_start
  cases cond
  · wp_auto
    iloeb as IH
    wp_pure
    iapply IH $$ Hpre HΦ
  · wp_end

end proof

end Perennial
