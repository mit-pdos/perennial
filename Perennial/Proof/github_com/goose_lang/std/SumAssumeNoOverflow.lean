/-
The proof of `github.com/goose-lang/std.SumAssumeNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.SumAssumeNoOverflow
public import Perennial.Spec.github_com.goose_lang.std.std_core.SumAssumeNoOverflow

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.SumAssumeNoOverflow.wp_proof
    (wp_SumAssumeNoOverflow : github_com.goose_lang.std.std_core.SumAssumeNoOverflow.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.SumAssumeNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start
  wp_auto
  wp_apply wp_SumAssumeNoOverflow as %H
  wp_end

end proof

end Perennial
