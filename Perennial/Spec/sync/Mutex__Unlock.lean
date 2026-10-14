/-
`sync.(*Mutex).Unlock`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- This form is useful for defer statements. -/
abbrev sync.Mutex.Unlock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isMutex m R ∗ ownMutex m ∗ ▷ R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
