/-
`internal/sync.(*Mutex).TryLock`'s spec.
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

abbrev internal.sync.Mutex.TryLock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.sync ∗ isLock m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"TryLock")) (Val #()))
    {{ (locked : Bool), RET #locked; if locked then ownLock m ∗ R else True }}

end spec

end Perennial
