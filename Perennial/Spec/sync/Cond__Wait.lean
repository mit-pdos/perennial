/-
`sync.(*Cond).Wait`'s spec, for a `Locker` (`isLocker`). The variant for a locker whose `Lock`
needs a resource (`isLockerWith`), `sync.Cond.wp_Wait_with`, is in `Perennial/Proof/sync/Results.lean`.
-/
module

public import Perennial.Proof.sync.CondDefs

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

abbrev sync.Cond.Wait.spec : Prop :=
  ∀ (c : Loc) (m : GoInterfaceOk) (R : IProp GF),
    {{ isCond c m ∗ isLocker m R ∗ R }}
      (App (Val (c @!! go.GoType.PointerType Cond.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); R }}

end spec

end Perennial
