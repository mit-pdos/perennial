/-
The proof of `github.com/tchajed/marshal.initialize'`.
-/
module

public import Perennial.Spec.github_com.tchajed.marshal.initialize
public import Perennial.Spec.github_com.goose_lang.std.initialize
public import Perennial.Spec.encoding.binary.initialize

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
variable [package_sem : github_com.tchajed.marshal.Assumptions]

theorem github_com.tchajed.marshal.initialize'.wp_proof
    (wp_std_initialize : github_com.goose_lang.std.initialize'.spec (GF := GF) (hG := hG))
    (wp_binary_initialize : encoding.binary.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.tchajed.marshal.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_std_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply wp_binary_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H2⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
