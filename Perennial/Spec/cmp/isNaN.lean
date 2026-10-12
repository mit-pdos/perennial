/-
`cmp.isNaN`'s spec (at `uint64`).
-/
module

public import Perennial.Proof.cmp.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

/-- `isNaN` on `uint64` is `false`: `x != x` never holds for an integer. -/
abbrev cmp.isNaN.spec : Prop :=
  ∀ (x : w64),
    {{ (True : IProp GF) }}
      (App (Val #(functions isNaN [go.uint64])) (Val #x))
    {{ RET #false; True }}

end spec

end Perennial
