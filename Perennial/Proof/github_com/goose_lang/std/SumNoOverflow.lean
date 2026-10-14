/-
The proof of `github.com/goose-lang/std.SumNoOverflow`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.SumNoOverflow
public import Perennial.Spec.github_com.goose_lang.std.std_core.SumNoOverflow

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.SumNoOverflow.wp_proof
    (wp_SumNoOverflow : github_com.goose_lang.std.std_core.SumNoOverflow.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.SumNoOverflow.spec (GF := GF) (hG := hG) := fun x y => by
  wp_start
  wp_auto
  wp_apply wp_SumNoOverflow
  wp_end

end proof

end Perennial
