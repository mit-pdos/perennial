/-
`strconv.NumError.Unwrap`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `e.Unwrap()`: `e.Err`; it only reads `e`. -/
abbrev strconv.NumError.Unwrap.spec : Prop :=
  ∀ (l : Loc) (v : strconv.NumError) (dq : DFrac),
    {{ (l ↦{dq} v : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType strconv.NumError.ty @!! go!"Unwrap")) (Val #()))
    {{ RET #v.Err'; l ↦{dq} v }}

end spec

end Perennial
