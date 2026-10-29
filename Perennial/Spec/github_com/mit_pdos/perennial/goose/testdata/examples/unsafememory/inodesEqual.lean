/-
`inodesEqual`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `inodesEqual(a, b)`: whether `a` and `b` hold the same inodes. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.spec : Prop :=
  ∀ (a b : GoSlice) (ma mb : List InodeM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory ∗ inodesOwn a ma ∗ inodesOwn b mb }}
      (App (App (Val (@! inodesEqual)) (Val #a)) (Val #b))
    {{ RET #(decide (ma = mb)); True }}

end spec

end Perennial
