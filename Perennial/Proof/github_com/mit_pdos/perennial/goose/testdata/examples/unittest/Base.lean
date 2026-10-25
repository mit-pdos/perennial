/-
Shared definitions of the proofs of some of the goose unit tests
(`goose/testdata/examples/unittest`): the package's `isPkgInit` and two tactic macros of the
proofs (`wp_auto_neg`, `wp_append_lit`).
-/
module

public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
public import Perennial.Golang.Theory.IfJoin
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.log.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.github_com.goose_lang.std.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest


section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unittest.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest :=
  build_get_is_pkg_init_wf

end wps

/-- `wp_auto`, also rewriting with a negated hypothesis `h : ¬ P` (to decide
`decide P` and `if P` as they appear). -/
macro "wp_auto_neg " h:ident : tactic =>
  `(tactic| repeat (first | wp_auto | simp only [$h:ident, decide_false, ↓reduceIte]))

set_option hygiene false in
/-- `arr = append(arr, []int{x})` (the slice is `Hz`, its capacity `Hzcap`). Used where
`go.SliceSemantics.composite_literal_slice` is not an instance: `wp_auto` unfolds slice
literals (`composite_literal_slice` is a pure step), but `wp_slice_literal` expects the
literal to be folded. -/
macro "wp_append_lit" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, _⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hz Hzcap Hsl2] with %sl1 ⟨Hz, Hzcap, _⟩
  · iframe
  try wp_auto))

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest

end Perennial
end
