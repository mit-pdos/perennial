/-
`pageSize`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `pageSize(inodes)` is the size of a leaf page holding `ms`: its header, then its body. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageSize.spec : Prop :=
  ∀ (s : GoSlice) (ms : List InodeM),
    {{ (inodesOwn s ms : IProp GF) }}
      (App (Val (@! pageSize)) (Val #s))
    {{ RET #(W64 ((16 + (pageBody true ms).length : Nat) : Int)); True }}

end spec

end Perennial
