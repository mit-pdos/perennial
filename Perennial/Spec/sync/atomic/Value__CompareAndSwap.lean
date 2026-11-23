/-
`sync.atomic.Value.CompareAndSwap`'s spec.
-/
module

public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- `CompareAndSwap(nil, new)` of a non-`nil` `new` on a `Value` owned by the caller that is
empty or holds a value of `new`'s dynamic type (Go panics otherwise): it stores `new` and returns
`true` exactly when the `Value` is empty. -/
abbrev sync.atomic.Value.CompareAndSwap.spec : Prop :=
  ∀ (u : Loc) (x new : GoInterface),
  new ≠ interface.nil → sameTypeOrNil x new →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ ownValue u (DFrac.own 1) x }}
    (App (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"CompareAndSwap"))
      (Val #interface.nil)) (Val #new))
  {{ (b : Bool), RET #b; ⌜b = true ↔ x = interface.nil⌝ ∗
      ownValue u (DFrac.own 1) (if b then new else x) }}

end spec

end Perennial
