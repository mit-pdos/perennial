/-
`cloneBytes`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `cloneBytes(v)` is a new slice holding the bytes of `v`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes.spec : Prop :=
  ∀ (v : GoSlice) (dq : DFrac) (bs : List w8),
    {{ (v ↦*{dq} bs : IProp GF) }}
      (App (Val (@! cloneBytes)) (Val #v))
    {{ (c : GoSlice), RET #c; v ↦*{dq} bs ∗ c ↦* bs }}

end spec

end Perennial
