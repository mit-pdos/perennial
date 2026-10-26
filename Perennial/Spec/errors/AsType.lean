/-
`errors.AsType`'s spec.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : errors.Assumptions]

/-- The parameter `S` and the precondition `isErrorTree S T' T ∗ ⌜S err⌝` specify the
methods of the errors in the tree of `err`; see the section comment. -/
abbrev errors.AsType.spec : Prop :=
  ∀ (S : GoError → Prop) (err : GoError) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T],
    {{ "#Htree" ∷ isErrorTree (GF := GF) S T' T ∗ "%HS" ∷ ⌜S err⌝ }}
      (App (Val #(functions AsType [T])) (Val #err))
    {{ (e : T') (found : Bool), RET (PairV #e #found); True }}

end spec

end Perennial
