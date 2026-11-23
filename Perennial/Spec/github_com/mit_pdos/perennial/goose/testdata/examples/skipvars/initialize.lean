/-
`github.com/mit-pdos/perennial/goose/testdata/examples/skipvars.initialize'`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Assumptions]

/-- The package's `initialize'`: the translated initializers of `first`, `mid` and `last`,
in Go's order; the skipped variables' initializers are not run. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars }}

end spec

end Perennial
