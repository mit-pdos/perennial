/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/user.LoadXIf`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.LoadXIf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.Assumptions]

/-- The branch that loads `dep.X` is not taken: `b` is false. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.LoadXIf.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.LoadXIf.spec (GF := GF) (hG := hG) := fun b => by
  wp_start as %Hb
  subst Hb
  wp_auto
  wp_end

end proof

end Perennial
