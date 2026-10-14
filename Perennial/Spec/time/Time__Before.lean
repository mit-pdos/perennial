/-
`time.Time.Before`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `Time.Before`: some `bool`. -/
abbrev time.Time.Before.spec : Prop :=
  ∀ (t u : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Before")) (Val #u))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
