/-
`time.runtimeIsBubbled`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `runtimeIsBubbled()` (true only inside a `testing/synctest` bubble; modeled in
`TrustedCode/time.lean` as an arbitrary boolean): some `bool`. -/
abbrev time.runtimeIsBubbled.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeIsBubbled)) (Val #()))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
