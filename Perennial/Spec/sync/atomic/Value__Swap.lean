/-
`sync.atomic.Value.Swap`'s spec.
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

/-- `Swap(v)` of a non-`nil` `v` in a `Value` that is empty or holds a value of `v`'s dynamic
type (Go panics otherwise); it returns the old content (`nil` if the `Value` was empty). -/
abbrev sync.atomic.Value.Swap.spec : Prop :=
  ∀ (u : Loc) (v : GoInterface),
  v ≠ interface.nil →
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ x : GoInterface, ownValue u (DFrac.own 1) x ∗ ⌜sameTypeOrNil x v⌝ ∗
      (ownValue u (DFrac.own 1) v ={∅,⊤}=∗ Φ #x)) -∗
    WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Swap")) (Val #v)) {{ Φ }}

end spec

end Perennial
