/-
The proof of `generics.useContainer`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useContainer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useContainer.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useContainer.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_map_make1 with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_end

end proof

end Perennial
