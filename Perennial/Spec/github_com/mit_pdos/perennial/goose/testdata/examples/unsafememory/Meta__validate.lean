/-
`(*Meta).validate`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta

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

/-- `m.validate()`: the magic, the version and the checksum (`metaSum`) are right. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.validate.spec : Prop :=
  ∀ (m : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta) (dq : DFrac),
    {{ (m ↦{dq} v ∗ ⌜0 < m.addr⌝ : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType Meta.ty @!! go!"validate")) (Val #()))
    {{ RET #(decide (v.magic' = W32 0xED0CDAED ∧ v.version' = W32 2 ∧
          v.checksum' = github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.metaSum v)); m ↦{dq} v }}

end spec

end Perennial
