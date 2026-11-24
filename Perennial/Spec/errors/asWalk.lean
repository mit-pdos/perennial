/-
`errors.asWalk`'s spec (the tree walk of the model of `As`, Go's `as`).
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

/-- `asWalk(err, target)` for a non-`nil` error `ii` and a target `*T`, `l` (`AsTarget T`):
* over an error tree `S` (`isErrorTree`, as `AsType`'s), each of whose errors the model decides
  (`AsDecided`): some result, `*l` written;
* when `ii` is assignable to `T` (`asAssignable`): `true`, `ii` stored (`asStored`; of the
  target's Lean type, `AsTypeTyped`), no method called;
* when the walk ends without a match after at most `n` calls of `Unwrap` (`asNoMatch`): `false`,
  the target unchanged. -/
abbrev errors.asWalk.spec : Prop :=
  (∀ (S : GoError → Prop) (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → (∀ ii', S (interface.ok ii') → AsDecided T ii') →
    {{ isErrorTree (GF := GF) S T' T ∗ ⌜S (interface.ok ii)⌝ ∗ l ↦ v }}
      (App (App (Val #(functions asWalk [])) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (b : Bool) (v' : T'), RET #b; l ↦ v' }}) ∧
  (∀ (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T → asAssignable T ii = true → AsTypeTyped T' T ii →
    {{ (l ↦ v : IProp GF) }}
      (App (App (Val #(functions asWalk [])) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (x : T'), RET #true; l ↦ x ∗ ⌜asStored T ii = #x⌝ }}) ∧
  (∀ (n : Nat) (ii : GoInterfaceOk) (l : Loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {T : go.GoType} [IntoValTyped (GF := GF) T' T] (v : T'),
    AsTarget T →
    {{ l ↦ v ∗ asNoMatch (GF := GF) T n (interface.ok ii) }}
      (App (App (Val #(functions asWalk [])) (Val #(interface.ok ii)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }})

end spec

end Perennial
