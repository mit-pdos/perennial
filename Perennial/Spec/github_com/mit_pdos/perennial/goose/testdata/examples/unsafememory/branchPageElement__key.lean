/-
`(*branchPageElement).key`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `n.key()` is the byte slice of the `ksize` bytes `pos` bytes past the element. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.branchPageElement.key.spec : Prop :=
  ∀ (n : Loc) (e : branchPageElement) (dq : DFrac),
    {{ (n ↦{dq} e ∗ ⌜0 < n.addr ∧ n.addr + uint.Z e.pos' + uint.Z e.ksize' ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (n @!! go.GoType.PointerType branchPageElement.ty @!! go!"key")) (Val #()))
    {{ RET #(slice.mk (n +ₗ uint.Z e.pos') (W64 (uint.Z e.ksize')) (W64 (uint.Z e.ksize')));
       n ↦{dq} e }}

end spec

end Perennial
