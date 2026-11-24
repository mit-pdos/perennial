/-
The proof of `github.com/mit-pdos/perennial/proph.NewProph`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.proph.NewProph

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.proph.Assumptions]

/-- From GooseLang's `NewProph` (`wp_new_proph`). -/
theorem github_com.mit_pdos.perennial.proph.NewProph.wp_proof :
    github_com.mit_pdos.perennial.proph.NewProph.spec (GF := GF) (hG := hG) := by
  wp_start as _
  wp_apply wp_new_proph as %pvs %p Hp
  iapply HΦ $$ %pvs %p Hp

end proof

end Perennial
