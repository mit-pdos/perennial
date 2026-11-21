/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/user.AddrX`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.AddrX

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.AddrX.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.AddrX.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
