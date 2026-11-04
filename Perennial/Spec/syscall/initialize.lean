/-
`syscall.initialize'`'s spec.
-/
module

public import Perennial.Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- The package's `initialize'`: initialize `sync`, then run the variable initializers and
`init` (the trusted models of `runtime_envs` and of `init.0`). -/
abbrev syscall.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.syscall get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.syscall }}

end spec

end Perennial
