/-
`cmp.Less`'s spec (at `uint64`).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

/-- `Less` on `uint64` is `<` on the unsigned values. -/
abbrev cmp.Less.spec : Prop :=
  ∀ (x y : w64),
    {{ (True : IProp GF) }}
      (App (App (Val #(functions Less [go.uint64])) (Val #x)) (Val #y))
    {{ (b : Bool), RET #b; ⌜b = true ↔ uint.Z x < uint.Z y⌝ }}

end spec

end Perennial
