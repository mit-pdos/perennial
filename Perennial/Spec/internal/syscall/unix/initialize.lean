/-
`internal.syscall.unix.initialize'`'s spec.
-/
module

public import Perennial.Proof.internal.syscall.unix.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.syscall.unix.Assumptions]

/-- The package's `initialize'`: initialize `syscall`, then store the function value
`faccessat = syscall.Faccessat`. -/
abbrev internal.syscall.unix.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.internal.syscall.unix get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }}
    (App (Val initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗
      isPkgInit (PROP := IProp GF) pkg_id.internal.syscall.unix }}

end spec

end Perennial
