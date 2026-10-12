/-
`strings.Builder.copyCheck`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `b.copyCheck()`, for a builder not copied by value (its `addr` is unset or `b`): sets `addr`
to `b`. -/
abbrev strings.Builder.copyCheck.spec : Prop :=
  ∀ (b addr : Loc) (buf : GoSlice), addr = null ∨ addr = b →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
        b ↦ ({ addr' := addr, buf' := buf } : Builder) }}
      (App (Val (b @!! go.GoType.PointerType Builder.ty @!! go!"copyCheck")) (Val #()))
    {{ RET #(); b ↦ ({ addr' := b, buf' := buf } : Builder) }}

end spec

end Perennial
