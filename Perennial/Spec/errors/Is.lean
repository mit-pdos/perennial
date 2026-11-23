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

/-- Spec of `errors.Is(err, target)`, for a `nil` target or one that `==` compares with the errors of
the tree of its type (`ComparableTarget`: a pointer error such as an `errors.New` error,
`comparableTarget_pointer`; an `Errno`, `comparableErr_uintptr`), whose type Go's `reflectlite`
finds comparable (the model's `true`). Its precondition is the error tree of `err`
(`errorWalkTree S I U target ∗ ⌜S err⌝`: the relations `I` and `U` say what each error's `Is` and
`Unwrap` methods may answer). It returns `err == target` if either is `nil`; otherwise an answer of
Go's walk of the tree (`IsWalk`): `true` at the first error that is `target` or whose `Is` returns
`true`, the children (`Unwrap`) walked in order. With exact relations the answer is a function of
the tree (`isWalk_det`); the over-approximating tree `errorIsTree S M target` gives
`errors.wp_Is_tree`'s post; `errors.wp_Is_ptr` is this spec for pointer targets.

For a `target` of another comparable type Go's `Is` compares it with the errors of the tree of
its type with `==`, which panics if they hold values that are not comparable (an interface field
holding a slice): `ComparableErr` asks that `==` on that type be the equality of plain values. -/
abbrev errors.Is.spec : Prop :=
  ∀ (S : GoError → Prop) (I : GoInterfaceOk → Bool → Prop)
    (U : GoInterfaceOk → List GoError → Prop) (err target : GoError),
    ComparableTarget S target →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ errorWalkTree (GF := GF) S I U target ∗
        ⌜S err⌝ }}
      (App (App (Val (@! Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b;
        ⌜(err = interface.nil ∨ target = interface.nil) → b = decide (err = target)⌝ ∗
        ⌜err ≠ interface.nil → target ≠ interface.nil → IsWalk true I U target err b⌝ }}

end spec

end Perennial
