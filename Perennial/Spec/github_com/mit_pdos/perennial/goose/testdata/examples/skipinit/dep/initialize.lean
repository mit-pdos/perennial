/-
`github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/dep.initialize'`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep.Assumptions]

/-- The package's `initialize'`: `X`'s initializer, which the model skips (`go.skipInit`). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep }}

end spec

end Perennial
