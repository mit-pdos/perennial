/-
The proof of `recoverNamed` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverNamed

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverNamed.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverNamed.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  -- the panic unwinds to the `Catch`, whose handler runs the deferred literal
  wp_apply wp_panic
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  itrivial

end proof

end Perennial
