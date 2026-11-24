/-
`internal.reflectlite.Value.assignTo`'s spec.
-/
module

public import Perennial.Proof.internal.reflectlite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

/-- `x.assignTo(context, dst, target)`, where the model decides it, in two cases:
* `dst` the token of a non-interface type `T` (of a kind, other than `Interface`) without type
  arguments (or a pointer to such, `go.identByName`), and `x` a `Value` of type `T` (direct or
  indirect): a `Value` of `T` holding `x`'s pointer, with `x`'s `flagIndir`;
* `dst` the token of an interface type `T`, `target` a pointer `l : *T`, and `x` the `Value` of
  a value `x : W` of a type `t` in `T`'s type set (`valueOfRepr`): `*l` set to the interface holding
  it (`y`), and the indirect `Value` of kind `Interface` holding `any(l)`. -/
abbrev internal.reflectlite.Value.assignTo.spec : Prop :=
  (∀ {T uT : go.GoType} [T ↓u uT] (kT : Nat) (xv : Value) (ctx : GoString) (target : GoInterface),
  go.kindOf uT = some kT → kT ≠ 20 → go.identByName T = true → xv.typ_' = go.tok T →
  (xv.flag' = W64 kT ∨ xv.flag' = W64 kT ||| W64 128) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (App (App (Val (xv @!! Value.ty @!! go!"assignTo")) (Val #ctx)) (Val #(go.tok T)))
        (Val #target))
    {{ (fl : w64), RET #(Value.mk (go.tok T) xv.ptr' fl); ⌜fl &&& W64 128 = xv.flag' &&& W64 128⌝ }}) ∧
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems] [IntoValTyped (GF := GF) V T]
    {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {t ut : go.GoType} [t ↓u ut]
    [IntoValTyped (GF := GF) W t] (kt : Nat) (xv : Value) (ctx : GoString) (l : Loc) (w y : V)
    (x : W),
  go.kindOf ut = some kt → go.isInterfaceType ut = false → go.isUntypedNil ut = false →
  go.typeSetContains t T = true → (#y : val) = #(interface.mkOk t #x) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite ∗ l ↦ w ∗
        internal.reflectlite.valueOfRepr (GF := GF) xv t kt x }}
      (App (App (App (Val (xv @!! Value.ty @!! go!"assignTo")) (Val #ctx)) (Val #(go.tok T)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ (fl : w64), RET #(Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #l) fl);
        ⌜fl &&& W64 128 = W64 128⌝ ∗ l ↦ y ∗
        internal.reflectlite.valueOfRepr (GF := GF) xv t kt x }})

end spec

end Perennial
