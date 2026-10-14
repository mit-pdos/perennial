/-
`errors.New`'s spec.
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

/-- `errors.New(msg)` returns an error (an `*errorString`) whose `Error()` returns `msg`; it is
a pointer error (`IsPointerError`). -/
abbrev errors.New.spec : Prop :=
  ∀ (msg : GoString),
    {{ (True : IProp GF) }}
      (App (Val (@! New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        ⌜IsPointerError err⌝ ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }}

end spec

end Perennial
