/-
`(*Page).leafPageElements`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `p.leafPageElements()` is the `[]leafPageElement` of the `p.count` elements after the header (nil for none). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElements.spec : Prop :=
  ∀ (p : Loc) (hdr : Page) (dq : DFrac),
    {{ (p ↦{dq} hdr ∗ ⌜0 < p.addr ∧ p.addr + 16 + 16 * uint.Z hdr.count' ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"leafPageElements")) (Val #()))
    {{ RET #(if hdr.count' = W16 0 then slice.nil
             else slice.mk (p +ₗ 16) (W64 (uint.Z hdr.count')) (W64 (uint.Z hdr.count')));
       p ↦{dq} hdr }}

end spec

end Perennial
