/-
`github.com/goose-lang/primitive.(*Mutex).Lock`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- `m.Lock()`: acquires the mutex, and with it its invariant `R`. -/
abbrev github_com.goose_lang.primitive.Mutex.Lock.spec : Prop :=
  ∀ (m : Loc) (R : IProp GF),
    {{ isMutex m R }}
      (App (Val (m @!! go.GoType.PointerType Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownMutex m ∗ R }}

end spec

end Perennial
