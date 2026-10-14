/-
`sync.(*Cond).Signal`'s spec.
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

abbrev sync.Cond.Signal.spec : Prop :=
  ∀ (c : Loc) (lk : GoInterfaceOk),
    {{ isCond (GF := GF) c lk }}
      (App (Val (c @!! go.GoType.PointerType Cond.ty @!! go!"Signal")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
