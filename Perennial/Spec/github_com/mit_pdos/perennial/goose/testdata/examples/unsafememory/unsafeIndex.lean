/-
`unsafeIndex`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `unsafeIndex(base, off, elemsz, n)` is `base` moved by `off + n * elemsz` bytes. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeIndex.spec : Prop :=
  ∀ (base : Loc) (off elemsz n : w64),
    {{ (⌜0 ≤ (base +ₗ sint.Z (off + n * elemsz)).addr ∧
          (base +ₗ sint.Z (off + n * elemsz)).addr ≤ maxAddr⌝ : IProp GF) }}
      (App (App (App (App (Val (@! unsafeIndex)) (Val #base)) (Val #off)) (Val #elemsz)) (Val #n))
    {{ RET #(base +ₗ sint.Z (off + n * elemsz)); True }}

end spec

end Perennial
