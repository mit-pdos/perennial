/-
`io.fs.initialize'`'s spec.
-/
module

public import Perennial.Proof.io.fs.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.fs.Assumptions]

/-- The package's `initialize'`: allocate the package's variables (the error variables, `SkipDir`,
`SkipAll`) and run their initializers, after initializing `time`, `internal/oserror`, `errors` and
`io`. -/
abbrev io.fs.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.io.fs get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.io.fs }}

end spec

end Perennial
