/-
The proof of `github.com/goose-lang/primitive.ProphId.Resolve`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.ProphId__Resolve

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
theorem github_com.goose_lang.primitive.ProphId.Resolve.wp_proof :
    github_com.goose_lang.primitive.ProphId.Resolve.spec (GF := GF) (hG := hG) := by
  intro p pvs v
  wp_start as Hp
  wp_apply wp_resolve_proph p pvs #v $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hpvs

end proof

end Perennial
