/-
`time.runtimeNano`'s spec.
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

/-- `runtimeNano()` (the `go:linkname`ed runtime clock, modeled in `TrustedCode/time.lean`): some
`int64`. -/
abbrev time.runtimeNano.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.runtimeNano)) (Val #()))
    {{ (x : w64), RET #x; True }}

end spec

end Perennial
