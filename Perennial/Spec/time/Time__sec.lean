/-
`time.Time.sec`'s spec.
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

/-- `(*Time).sec()`: some `int64`; `*t` unchanged. -/
abbrev time.Time.sec.spec : Prop :=
  ∀ (t : Loc) (tv : time.Time),
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType time.Time.ty @!! go!"sec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }}

end spec

end Perennial
