/-
The proof of `github.com/goose-lang/primitive.RandomUint64`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

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

/-- Unfolds the call to `RandomUint64.impl` (the shared `wp_RandomUint64__impl`). -/
theorem github_com.goose_lang.primitive.RandomUint64.wp_proof :
    github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG) := by
  wp_start_folded as _
  wp_func_call
  iapply «wp_RandomUint64__impl» $$ [] HΦ
  itrivial

end proof

end Perennial
