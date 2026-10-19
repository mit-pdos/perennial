/-
The proof of `github.com/goose-lang/primitive.ProphId.ResolveBool`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.ProphId__ResolveBool

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- From GooseLang's `ResolveProph` (`wp_resolve_proph`). -/
theorem github_com.goose_lang.primitive.ProphId.ResolveBool.wp_proof :
    github_com.goose_lang.primitive.ProphId.ResolveBool.spec (GF := GF) (hG := hG) := by
  intro p pvs b
  wp_start as Hp
  wp_apply wp_resolve_proph p pvs #b $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hpvs

end proof

end Perennial
