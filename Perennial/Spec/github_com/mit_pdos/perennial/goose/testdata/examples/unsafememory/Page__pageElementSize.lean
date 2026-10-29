/-
`(*Page).pageElementSize`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `p.pageElementSize()` is 16 for a leaf and for a branch page. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.pageElementSize.spec : Prop :=
  ∀ (p : Loc) (hdr : Page) (dq : DFrac),
    {{ (p ↦{dq} hdr ∗ ⌜p ≠ null⌝ : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"pageElementSize")) (Val #()))
    {{ RET #(W64 16); p ↦{dq} hdr }}

end spec

end Perennial
