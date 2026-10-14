/-
`time.subMono`'s spec.
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

/-- Spec of `subMono`: some duration. -/
abbrev time.subMono.spec : Prop :=
  ∀ (t u : w64),
    {{ (True : IProp GF) }}
      (App (App (Val (@! time.subMono)) (Val #t)) (Val #u))
    {{ (d : w64), RET #d; True }}

end spec

end Perennial
