/-
`pageAt`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `pageAt(buf, off)` is the address of byte `off` of `buf`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.spec : Prop :=
  ∀ (buf : GoSlice) (off : w64),
    {{ (⌜0 < buf.ptr.addr ∧ 0 ≤ sint.Z off ∧ sint.Z off < sint.Z buf.len⌝ : IProp GF) }}
      (App (App (Val (@! pageAt)) (Val #buf)) (Val #off))
    {{ RET #(buf.ptr +ₗ sint.Z off); True }}

end spec

end Perennial
