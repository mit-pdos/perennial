/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.ifJoinDemo`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.ifJoinDemo

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

-- Workaround: `wp_auto` unfolds slice literals (`composite_literal_slice` is a
-- pure step), but `wp_slice_literal` expects the literal to be folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

/-- Case-splits the rest of the function on `arg1`; `wp_ifJoinDemo_join` (in `Results`) joins the branches of the first `if` with `wp_if_join` instead. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.ifJoinDemo.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.ifJoinDemo.spec (GF := GF) (hG := hG) := fun arg1 arg2 => by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hz, Hzcap⟩
  wp_auto
  cases arg1
  · wp_auto
    cases arg2
    · wp_auto; wp_end
    · wp_auto; wp_append_lit; wp_end
  · wp_auto
    wp_append_lit
    cases arg2
    · wp_auto; wp_end
    · wp_auto; wp_append_lit; wp_end

end proof

end Perennial
