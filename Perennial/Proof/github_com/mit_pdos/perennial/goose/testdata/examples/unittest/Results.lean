/-
What the proofs of the goose unit tests show beyond the linked results: a second proof of
`ifJoinDemo`'s triple, with `wp_if_join`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unittest.Assumptions]

-- Workaround: `wp_auto` unfolds slice literals (`composite_literal_slice` is a
-- pure step), but `wp_slice_literal` expects the literal to be folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

/-- An alternative proof of `wp_ifJoinDemo`, which joins the branches of the first
`if` with `wp_if_join` instead of case-splitting the rest of the function. -/
theorem wp_ifJoinDemo_join : ifJoinDemo.spec (GF := GF) (hG := hG) := fun arg1 arg2 => by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hz, Hzcap⟩
  wp_auto
  wp_if_join (fun v => (iprop(⌜v = executeVal⌝ ∗
      ∃ (sl : GoSlice) (xs : List w64),
        arr_ptr ↦ sl ∗ sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1)) : IProp GF))
    with [arr Hz Hzcap]
  · -- `arg1 = false`
    isplitr
    · ipureintro; trivial
    iexists _; iexists _; iframe
  · -- `arg1 = true`
    wp_append_lit
    isplitr
    · ipureintro; trivial
    iexists _; iexists _; iframe
  · iintro %v ⟨%Hv, %sl1, %xs, arr, Hz, Hzcap⟩
    subst Hv
    wp_auto
    wp_if_destruct
    · wp_end
    · wp_append_lit; wp_end

end results

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest

end Perennial
