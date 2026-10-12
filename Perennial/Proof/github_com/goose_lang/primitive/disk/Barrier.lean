/-
The proof of `github.com/goose-lang/primitive/disk.Barrier`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.disk.Barrier

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode disk_ffi

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.disk.Assumptions]

theorem github_com.goose_lang.primitive.disk.Barrier.wp_proof :
    github_com.goose_lang.primitive.disk.Barrier.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_end

end proof

end Perennial
