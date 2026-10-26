/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs.initialize'`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.initialize
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.initialize
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext net_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.netfs.initialize'.wp_proof
    (wp_fsext_initialize' : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.initialize'.spec (GF := GF) (hG := hG))
    (wp_netext_initialize' : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.netfs.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_netext_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hnet⟩
  wp_apply wp_fsext_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hfs⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
