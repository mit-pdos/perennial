/-
`sync.(*Mutex).Lock`'s spec.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

abbrev sync.Mutex.Lock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownMutex m ∗ R }}

end spec

end Perennial
