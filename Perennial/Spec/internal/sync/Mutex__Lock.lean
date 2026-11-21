/-
`internal/sync.(*Mutex).Lock`'s spec.
-/
module

public import Perennial.Proof.internal.sync.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

abbrev internal.sync.Mutex.Lock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.sync ∗ isLock m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownLock m ∗ R }}

end spec

end Perennial
