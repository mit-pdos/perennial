/-
`(*Page).meta`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `p.meta()` is the address 16 bytes past `p`, after the page header. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.«meta».spec : Prop :=
  ∀ (p : Loc),
    {{ (⌜0 < p.addr ∧ p.addr + 16 ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"meta")) (Val #()))
    {{ RET #(p +ₗ 16); True }}

end spec

end Perennial
