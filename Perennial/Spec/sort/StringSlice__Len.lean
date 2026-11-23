/-
`sort.StringSlice.Len`'s spec.
-/
module

public import Perennial.Proof.sort.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `x.Len()` for `x` a `StringSlice`: its length. -/
abbrev sort.StringSlice.Len.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString) (dq : DFrac),
    {{ (x ↦*{dq} xs : IProp GF) }}
      (App (Val (x @!! sort.StringSlice.ty @!! go!"Len")) (Val #()))
    {{ RET #(W64 xs.length); x ↦*{dq} xs }}

end spec

end Perennial
