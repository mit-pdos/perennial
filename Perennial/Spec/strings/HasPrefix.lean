/-
`strings.HasPrefix`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. -/
abbrev strings.HasPrefix.spec : Prop :=
  ∀ (s pfx : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! HasPrefix)) (Val #s)) (Val #pfx))
    {{ RET #(decide (pfx <+: s)); True }}

end spec

end Perennial
