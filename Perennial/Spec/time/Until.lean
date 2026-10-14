/-
`time.Until`'s spec.
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

/-- Spec of `time.Until`: some duration (`t.Sub(Now())`, or the current monotonic reading
subtracted from `t`'s). It reads the global `startNano` (`isPkgInit`). -/
abbrev time.Until.spec : Prop :=
  ∀ (t : time.Time),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.Until)) (Val #t))
    {{ (d : w64), RET #d; True }}

end spec

end Perennial
