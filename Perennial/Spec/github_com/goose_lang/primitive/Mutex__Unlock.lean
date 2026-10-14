/-
`github.com/goose-lang/primitive.(*Mutex).Unlock`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- This form is useful for defer statements. -/
abbrev github_com.goose_lang.primitive.Mutex.Unlock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isMutex m R ∗ ownMutex m ∗ ▷ R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
