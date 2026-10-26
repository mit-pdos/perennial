/-
The proof of `github.com/goose-lang/primitive.ProphId.ResolveU64`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.ProphId__ResolveU64

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

/-- From GooseLang's `ResolveProph` (`wp_resolve_proph`). -/
theorem github_com.goose_lang.primitive.ProphId.ResolveU64.wp_proof :
    github_com.goose_lang.primitive.ProphId.ResolveU64.spec (GF := GF) (hG := hG) := by
  intro p pvs x
  wp_start as Hp
  wp_apply wp_resolve_proph p pvs #x $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hpvs

end proof

end Perennial
