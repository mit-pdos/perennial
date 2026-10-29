/-
`(*leafPageElement).value`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `n.value()` is the byte slice of the `vsize` bytes after the key. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.value.spec : Prop :=
  ∀ (n : Loc) (e : leafPageElement) (dq : DFrac),
    {{ (n ↦{dq} e ∗ ⌜0 < n.addr ∧
          n.addr + uint.Z e.pos' + uint.Z e.ksize' + uint.Z e.vsize' ≤ maxAddr⌝ : IProp GF) }}
      (App (Val (n @!! go.GoType.PointerType leafPageElement.ty @!! go!"value")) (Val #()))
    {{ RET #(slice.mk (n +ₗ (uint.Z e.pos' + uint.Z e.ksize')) (W64 (uint.Z e.vsize'))
             (W64 (uint.Z e.vsize')));
       n ↦{dq} e }}

end spec

end Perennial
