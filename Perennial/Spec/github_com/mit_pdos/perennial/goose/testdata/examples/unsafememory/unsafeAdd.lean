/-
`unsafeAdd`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `unsafeAdd(base, off)` is `base` moved by `off` bytes, for a result in `[0, maxAddr]`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd.spec : Prop :=
  ∀ (base : Loc) (off : w64),
    {{ (⌜0 ≤ (base +ₗ sint.Z off).addr ∧ (base +ₗ sint.Z off).addr ≤ maxAddr⌝ : IProp GF) }}
      (App (App (Val (@! unsafeAdd)) (Val #base)) (Val #off))
    {{ RET #(base +ₗ sint.Z off); True }}

end spec

end Perennial
