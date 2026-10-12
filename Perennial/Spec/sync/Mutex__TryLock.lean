/-
`sync.(*Mutex).TryLock`'s spec.
-/
module

public import Perennial.Proof.sync.Base

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

abbrev sync.Mutex.TryLock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"TryLock")) (Val #()))
    {{ (locked : Bool), RET #locked; if locked then ownMutex m ∗ R else True }}

end spec

end Perennial
