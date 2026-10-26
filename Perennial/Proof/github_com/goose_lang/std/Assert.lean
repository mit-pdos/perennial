/-
The proof of `github.com/goose-lang/std.Assert`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.Assert

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.Assert.wp_proof :
    github_com.goose_lang.std.Assert.spec (GF := GF) (hG := hG) := fun cond => by
  wp_start as %Hc
  subst Hc
  wp_auto
  wp_end

end proof

end Perennial
