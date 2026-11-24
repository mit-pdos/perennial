/-
`internal.reflectlite.Value.Set`'s spec.
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

/-- `v.Set(x)` of the addressable `Value` of the variable `l : *T` (`Elem()` of `ValueOf(any(l))`),
in two cases:
* a non-interface `T` (of a kind) without type arguments (or a pointer to such, `go.identByName`),
  and `x` the `Value` of a value `y : V` of `T` (`valueOfRepr`): `*l = y`;
* an interface type `T`, and `x` the `Value` of a value `x : W` of a non-interface type `t` (of a
  kind) in `T`'s type set: `*l` set to `y`, the interface holding `x`. -/
abbrev internal.reflectlite.Value.Set.spec : Prop :=
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T uT : go.GoType} [T ↓u uT]
    [IntoValTyped (GF := GF) V T] (kT : Nat) (l : Loc) (w y : V) (xv : Value),
  go.kindOf uT = some kT → go.isInterfaceType uT = false → go.isUntypedNil uT = false →
  go.identByName T = true →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite ∗ l ↦ w ∗
        internal.reflectlite.valueOfRepr (GF := GF) xv T kT y }}
      (App (Val ((Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #l)
        (W64 kT ||| W64 128 ||| W64 256)) @!! Value.ty @!! go!"Set")) (Val #xv))
    {{ RET #(); l ↦ y }}) ∧
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems] [IntoValTyped (GF := GF) V T]
    {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {t ut : go.GoType} [t ↓u ut]
    [IntoValTyped (GF := GF) W t] (kt : Nat) (l : Loc) (w y : V) (x : W) (xv : Value),
  go.kindOf ut = some kt → go.isInterfaceType ut = false → go.isUntypedNil ut = false →
  go.typeSetContains t T = true → (#y : val) = #(interface.mkOk t #x) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite ∗ l ↦ w ∗
        internal.reflectlite.valueOfRepr (GF := GF) xv t kt x }}
      (App (Val ((Value.mk (go.tok T) (interface.mkOk (go.PointerType T) #l)
        (W64 20 ||| W64 128 ||| W64 256)) @!! Value.ty @!! go!"Set")) (Val #xv))
    {{ RET #(); l ↦ y }})

end spec

end Perennial
