/-
`errors.Join`'s spec.
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

/-- `errors.Join(errs...)`: `nil` exactly when every error of `errs` is `nil` (else a fresh
`*joinError` of the non-nil ones). The slice is only read. -/
abbrev errors.Join.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List GoInterface),
    {{ (sl ↦*{dq} es : IProp GF) }}
      (App (Val (@! Join)) (Val #sl))
    {{ (e : GoInterface), RET #e;
        ⌜e = interface.nil ↔ ∀ x ∈ es, x = interface.nil⌝ ∗ sl ↦*{dq} es }}

end spec

end Perennial
