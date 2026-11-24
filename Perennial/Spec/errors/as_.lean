/-
`errors.as`'s spec.
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

/-- Spec of `as(err, target, targetVal, targetType)` (`wrap.go`, `As`'s tree walk) for a non-`nil`
error `ii` and a target `*T`, `l`, with `As`'s `targetVal` (`ValueOf(target)`, `asTargetVal`) and
`targetType` (its `Type().Elem()`, `asTargetType`), in `errors.As`'s three cases:
* over an error tree `S` (`isErrorTree`), each of whose errors the model decides (`AsDecided`,
  `asRepr`): some result, `*l` written;
* when `ii` is assignable to `T` (`asAssignable`): `true`, `ii` stored (`asStored`);
* when the walk ends without a match after at most `n` calls of `Unwrap` (`asNoMatch`): `false`,
  the target unchanged. -/
abbrev errors.«as».spec : Prop :=
  (∀ (S : GoError → Prop) (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → (∀ ii', S (interface.ok ii') → AsDecided T ii' ∧ asRepr (GF := GF) T ii') →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ isErrorTree (GF := GF) S T' T ∗
        ⌜S (interface.ok ii)⌝ ∗ l ↦ v }}
      (App (App (App (App (Val (@! errors.as')) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(errors.asTargetVal T l)))
        (Val #(errors.asTargetType T)))
    {{ (b : Bool), RET #b; ∃ v' : T', l ↦ v' }}) ∧
  (∀ (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → AsDecided T ii → asRepr (GF := GF) T ii → asAssignable T ii = true →
    AsTypeTyped T' T ii →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (App (App (Val (@! errors.as')) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(errors.asTargetVal T l)))
        (Val #(errors.asTargetType T)))
    {{ (b : Bool), RET #b; ⌜b = true⌝ ∗ ∃ x : T', l ↦ x ∗ ⌜asStored T ii = #x⌝ }}) ∧
  (∀ (n : Nat) (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v ∗
        asNoMatch (GF := GF) T n (interface.ok ii) }}
      (App (App (App (App (Val (@! errors.as')) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(errors.asTargetVal T l)))
        (Val #(errors.asTargetType T)))
    {{ (b : Bool), RET #b; ⌜b = false⌝ ∗ l ↦ v }})

end spec

end Perennial
