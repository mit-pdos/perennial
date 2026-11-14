/-
`errors.As`'s spec.
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

/-- Spec of `errors.As(err, target)` for a target `*T`, `l` (axiom). `As` walks the error tree of
`err` as `AsType[T]` does, calling the `As` methods with `target` itself, and stores a matching
error in `*l`; it finds the target's type by reflection (`internal/reflectlite`, not translated).

Its precondition is either of:
* `err`'s own dynamic type matches `T` (`AsFirst T err #x`): Go's `as` tests that first and, when
  it holds, stores `err`'s value `x` and returns `true` without calling any method of `err`, so no
  error tree is needed;
* the error tree of `err` (`wp_AsType`'s precondition: `isErrorTree S T' T ∗ ⌜S err⌝`).
It returns some `b` and leaves some `v'` in `*l`, and in the first case `true` and `x`.

Go's `As` panics when `target` is `nil`, is not a non-`nil` pointer, or points to a type that
is neither an interface type nor implements `error`. The target here is the pointer `l` of type
`*T`, and `l ↦ v` implies `l ≠ null`; the premise `AsTarget T` excludes the third panic.

It is not proved from a translation of `As` as `Is` is (`wp_Is`): `As` and `as` use reflection
throughout (`reflectlite.ValueOf(target)`, `Kind`, `IsNil`, `Elem`, `Implements(errorType)`,
`TypeOf(err).AssignableTo(targetType)`, `targetVal.Elem().Set(ValueOf(err))`), with the target
type a run-time value, so a model would replace most of `as` by axioms about typed reflection
(what `AsTypeTyped` assumes for `AsType`), not a few small ones. -/
abbrev errors.As.spec : Prop :=
  ∀ (S : GoError → Prop) (err : GoError) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v x : T'),
    AsTarget T →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗
        (⌜AsFirst T err #x⌝ ∨ isErrorTree (GF := GF) S T' T ∗ ⌜S err⌝) ∗ l ↦ v }}
      (App (App (Val (@! As)) (Val #err)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (b : Bool) (v' : T'), RET #b; l ↦ v' ∗ ⌜AsFirst T err #x → b = true ∧ v' = x⌝ }}

end spec

end Perennial
