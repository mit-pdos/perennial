/-
`errors.Unwrap`'s spec.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

abbrev errors.Unwrap.spec : Prop :=
  ∀ (err : GoError),
    {{ isUnwrappable (GF := GF) err }}
      (App (Val (@! Unwrap)) (Val #err))
    {{ (err' : GoError), RET #err'; True }}

end spec

end Perennial
