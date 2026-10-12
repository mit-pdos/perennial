/-
`sync.(*RWMutex).RLocker`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `rw.RLocker()` is `Locker((*rlocker)(rw))`. -/
abbrev sync.RWMutex.RLocker.spec : Prop :=
  ∀ (rw : Loc),
    {{ (True : IProp GF) }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLocker")) (Val #()))
    {{ RET #(GoInterface.ok (rlockerOf rw)); True }}

end spec

end Perennial
