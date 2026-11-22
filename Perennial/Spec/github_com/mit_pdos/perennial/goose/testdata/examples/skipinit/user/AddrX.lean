/-
`github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/user.AddrX`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.Assumptions]

/-- `AddrX()` returns `dep.X`'s address, though `dep.X` is not allocated (its initializer is
skipped, `go.skipInit`): taking the address of a skipped variable is fine. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.AddrX.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user }}
      (App (Val (@! AddrX)) (Val #()))
    {{ RET #(globalAddr github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep.X); True }}

end spec

end Perennial
