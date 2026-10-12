/-
`time.Sleep`'s spec.
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

/-- `time.Sleep(d)`: returns (the model ignores the delay). -/
abbrev time.Sleep.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (@! time.Sleep)) (Val #d))
    {{ RET #(); True }}

end spec

end Perennial
