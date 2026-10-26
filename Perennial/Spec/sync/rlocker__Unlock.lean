/-
`sync.(*rlocker).Unlock`'s spec.
-/
module

public import Perennial.Proof.sync.RWMutexGuard

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

/-- `(*rlocker)(rw).Unlock()` is `rw.RUnlock()`. -/
abbrev sync.rlocker.Unlock.spec : Prop :=
  ∀ (rw : Loc) (P : Qp → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexRLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.GoType.PointerType rlocker.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }}

end spec

end Perennial
