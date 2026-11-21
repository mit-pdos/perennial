/-
`github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/user.LoadXIf`'s spec.
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

/-- `LoadXIf(b)` with `b` false returns `0`. The precondition `b = false` is what makes it
provable: the branch taken when `b` holds loads `dep.X`, which is not allocated (its initializer
is skipped, `go.skipInit`), a stuck load with no proof. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.LoadXIf.spec : Prop :=
  ∀ (b : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user ∗ ⌜b = false⌝ }}
      (App (Val (@! LoadXIf)) (Val #b))
    {{ RET #(W64 0); True }}

end spec

end Perennial
