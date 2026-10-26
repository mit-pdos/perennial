/-
`errors.Is`'s spec.
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

/-- Spec of `errors.Is(err, target)`, for a `nil` or pointer `target` (`IsPointerError`, such as
an `errors.New` error), whose type Go's `reflectlite` finds comparable (the model's `true`).
Its precondition is the error tree of `err`
(`errorIsTree S M target ∗ ⌜S err⌝`), whose errors of `target`'s type hold pointers
(`TreeTyped`, Go's typing). It returns `err == target` if either is `nil`; otherwise `true` if
`err == target` (its first check), and `true` only if some error of the tree is `target` or has
an `Is` method that returned `true` (`M`).

For a `target` of another comparable type Go's `Is` compares it with the errors of the tree of
its type with `==`, which panics if they hold values that are not comparable (an interface field
holding a slice): so `target` is restricted to pointers. -/
abbrev errors.Is.spec : Prop :=
  ∀ (S : GoError → Prop) (M : GoInterfaceOk → Prop) (err target : GoError),
    (∀ tii, target = interface.ok tii → IsPointerError tii) →
    TreeTyped S target →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errorIsTree (GF := GF) S M target ∗ ⌜S err⌝ }}
      (App (App (Val (@! Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b;
        ⌜(err = interface.nil ∨ target = interface.nil) → b = decide (err = target)⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err = target → b = true⌝ ∗
        ⌜∀ tii, target = interface.ok tii → IsPointerError tii → err ≠ interface.nil →
          b = true → ∃ ii, S (interface.ok ii) ∧ (interface.ok ii = target ∨ M ii)⌝ }}

end spec

end Perennial
