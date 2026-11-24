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

/-- Spec of `errors.As(err, target)` for a target `*T`, `l`. `As` and its tree walk `as` are Go's
(`src/errors/wrap.go`, translated with their bodies), over the Go model of `internal/reflectlite`
(`goose/model/overlay/internal/reflectlite`: the checks of the target, `TypeOf(err).AssignableTo(T)`
and the store, `Value.Set`).

Go's `As` panics when `target` is `nil`, is not a non-`nil` pointer, or points to a type that
is neither an interface type nor implements `error`. The target here is the pointer `l` of type
`*T`, and `l ↦ v` implies `l ≠ null`; the premise `AsTarget T` excludes the third panic.

Three cases:
* over an error tree `S` of `err` (`isErrorTree`, as `AsType`'s: the `As` methods called with
  `target` itself), each of whose errors the model decides (`AsDecided`: it does not decide Go's
  assignability of a type to another of the same underlying type, one of them unnamed, nor for
  struct, channel and function kinds, and finds an error of a non-interface type `T` only for a
  `T` named or a pointer to a named type; and the model's reflection on each error is defined, with
  a Lean representation of its type for an interface `T`, `asRepr`): some
  result, `*l` written;
* **first match**: `err`'s dynamic type is assignable to `T` (`asAssignable`: implements an
  interface `T`, or is `T`; decided by the model, `AsDecided`): `true`, `err` stored into `*l` (`asStored`; of the target's Lean type,
  `AsTypeTyped`), no method of `err` called;
* **no match**: `err` is `nil`, or its walk ends without a match after at most `n` calls of
  `Unwrap` (`asNoMatch`: leaves and `Unwrap() error` wrappers not assignable to `T`, without an
  `As(any) bool` method): `false`, the target unchanged. -/
abbrev errors.As.spec : Prop :=
  (∀ (S : GoError → Prop) (err : GoError) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → (∀ ii, S (interface.ok ii) → AsDecided T ii ∧ asRepr (GF := GF) T ii) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isErrorTree (GF := GF) S T' T ∗ ⌜S err⌝ ∗
        l ↦ v }}
      (App (App (Val (@! As)) (Val #err)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (b : Bool) (v' : T'), RET #b; l ↦ v' }}) ∧
  (∀ (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → AsDecided T ii → asRepr (GF := GF) T ii → asAssignable T ii = true →
    AsTypeTyped T' T ii →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (Val (@! As)) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (x : T'), RET #true; l ↦ x ∗ ⌜asStored T ii = #x⌝ }}) ∧
  (∀ (n : Nat) (err : GoError) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v ∗ asNoMatch (GF := GF) T n err }}
      (App (App (Val (@! As)) (Val #err)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }})

end spec

end Perennial
