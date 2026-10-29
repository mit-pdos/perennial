/-
`(*Meta).write`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `m.write(p)` sets `m`'s checksum (`metaSum`), the page's id (`txid % 2`) and flags
(`metaPageFlag`), and copies `*m` to the meta after the page header. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.write.spec : Prop :=
  ∀ (m p : Loc) (v : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta) (hdr : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page) (old : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta),
    {{ (m ↦ v ∗ p ↦ hdr ∗ (p +ₗ 16) ↦ old ∗ ⌜0 < m.addr ∧ 0 < p.addr⌝ : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType Meta.ty @!! go!"write")) (Val #p))
    {{ RET #();
        m ↦ { v with checksum' := github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.metaSum v } ∗
        p ↦ { hdr with id' := v.txid' % W64 2, flags' := W16 4 } ∗
        (p +ₗ 16) ↦ { v with checksum' := github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.metaSum v } }}

end spec

end Perennial
