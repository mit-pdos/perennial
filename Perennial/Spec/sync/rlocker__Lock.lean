/-
`sync.(*rlocker).Lock`'s spec.
-/
module

public import Perennial.Proof.sync.RWMutexGuard

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `(*rlocker)(rw).Lock()` is `rw.RLock()`. -/
abbrev sync.rlocker.Lock.spec : Prop :=
  ∀ (rw : Loc) (P : Qp → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType rlocker.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexRLocked rw P ∗ ▷ P rfrac }}

end spec

end Perennial
