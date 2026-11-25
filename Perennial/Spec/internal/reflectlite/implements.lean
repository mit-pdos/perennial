/-
`internal.reflectlite.implements`'s spec.
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

/-- `implements(T, V)` of the token of a type `T` and a type `V`:
* for a non-interface `T` (of a kind other than `Interface`), false;
* for an interface type `T` and the token of a non-interface type `V` (of a kind; represented by a
  Lean type `W`), whether `V` is in `T`'s type set. -/
abbrev internal.reflectlite.implements.spec : Prop :=
  (∀ {T uT : go.GoType} [T ↓u uT] [go.NotLayoutModelled T] (kT : Nat) (v : GoInterface),
  go.kindOf uT = some kT → kT ≠ 20 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (App (Val (@! implements)) (Val #(go.tok T))) (Val #v))
    {{ RET #false; True }}) ∧
  (∀ {T : go.GoType} {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems]
    [go.NotLayoutModelled T]
    {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {V uV : go.GoType} [V ↓u uV]
    [go.NotLayoutModelled V] [IntoValTyped (GF := GF) W V] (kV : Nat),
  go.kindOf uV = some kV → go.isInterfaceType uV = false → go.isUntypedNil uV = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (App (Val (@! implements)) (Val #(go.tok T))) (Val #(go.tok V)))
    {{ RET #(go.typeSetContains V T); True }})

end spec

end Perennial
