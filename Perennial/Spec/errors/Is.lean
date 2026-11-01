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
Its precondition is the error tree of `err` (`errorWalkTree S I U target ∗ ⌜S err⌝`: the
relations `I` and `U` say what each error's `Is` and `Unwrap` methods may answer), whose errors
of `target`'s type hold pointers (`TreeTyped`, Go's typing). It returns `err == target` if either
is `nil`; otherwise an answer of Go's walk of the tree (`IsWalk`): `true` at the first error that
is `target` or whose `Is` returns `true`, the children (`Unwrap`) walked in order. With exact
relations the answer is a function of the tree (`isWalk_det`); the over-approximating tree
`errorIsTree S M target` gives `errors.Is.spec_tree`'s post.

For a `target` of another comparable type Go's `Is` compares it with the errors of the tree of
its type with `==`, which panics if they hold values that are not comparable (an interface field
holding a slice): so `target` is restricted to pointers. -/
abbrev errors.Is.spec : Prop :=
  ∀ (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (err target : GoError),
    (∀ tii, target = interface.ok tii → IsPointerError tii) →
    TreeTyped S target →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errorWalkTree (GF := GF) S I U target ∗
        ⌜S err⌝ }}
      (App (App (Val (@! Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b;
        ⌜(err = interface.nil ∨ target = interface.nil) → b = decide (err = target)⌝ ∗
        ⌜err ≠ interface.nil → target ≠ interface.nil → IsWalk true I U target err b⌝ }}

end spec

end Perennial
