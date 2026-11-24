/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/grovefile.initialize'`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.initialize
public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.initialize'.wp_proof
    (wp_grove_ffi_initialize' : github_com.mit_pdos.gokv.grove_ffi.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_grove_ffi_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hgrove⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
