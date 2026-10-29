/-
`(*Page).branchPageElement`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `p.branchPageElement(i)` is the address `16 + 16 i` bytes past `p`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.branchPageElement.spec : Prop :=
  ∀ (p : Loc) (idx : w16),
    {{ (⌜0 < p.addr ∧ p.addr + 16 + 16 * uint.Z idx ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"branchPageElement")) (Val #idx))
    {{ RET #(p +ₗ (16 + 16 * uint.Z idx)); True }}

end spec

end Perennial
