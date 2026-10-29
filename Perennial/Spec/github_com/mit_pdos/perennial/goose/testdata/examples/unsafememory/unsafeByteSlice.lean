/-
`unsafeByteSlice`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `unsafeByteSlice(base, off, i, j)` is the byte slice of the bytes `i` to `j` from `base + off`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice.spec : Prop :=
  ∀ (base : Loc) (off i j : w64),
    {{ (⌜0 < (base +ₗ sint.Z off).addr ∧ (base +ₗ sint.Z off).addr + sint.Z j ≤ maxAddr ∧
          0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j⌝ : IProp GF) }}
      (App (App (App (App (Val (@! unsafeByteSlice)) (Val #base)) (Val #off)) (Val #i)) (Val #j))
    {{ RET #(slice.mk ((base +ₗ sint.Z off) +ₗ sint.Z i) (j - i) (j - i)); True }}

end spec

end Perennial
