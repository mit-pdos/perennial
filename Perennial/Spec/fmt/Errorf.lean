/-
`fmt.Errorf`'s spec.
-/
module

public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.Errorf(format, args...)` returns a non-nil error whose `Error()` returns some string.
The model of `Errorf` (`Perennial/TrustedCode/fmt.lean`) does not format: it is
`errors.New(format)`, ignoring the arguments, so this follows from `errors.wp_New`. (The
statement does not give back `args_sl ↦* args`, which the model never reads.) The arguments must
be of predeclared basic types (`ArgsWf`): Go's `Errorf` calls the `Error()`/`String()` methods of
other arguments, which the model does not, so for them it could panic or have effects the model
lacks. -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny),
  ArgsWf args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }}

end spec

end Perennial
