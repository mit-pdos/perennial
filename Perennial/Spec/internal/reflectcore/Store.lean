/-
`internal.reflectcore.Store`'s spec.
-/
module

public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

/-- `Store(p, x)` of `any(p)` for `p : *T`: `store[T](p, x)`: `*p = x.(T)`, for a non-interface `T`
and `x` holding a `T`, or an interface type `T` and `x` in `T`'s type set. -/
abbrev internal.reflectcore.Store.spec : Prop :=
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T Tu : go.GoType} [T ↓u Tu]
    [IntoValTyped (GF := GF) V T] (l : Loc) (v y : V),
  go.isInterfaceType Tu = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore ∗ l ↦ v }}
      (App (App (Val (@! Store)) (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(interface.mkOk T #y)))
    {{ RET #(); l ↦ y }}) ∧
  (∀ {T : go.GoType} {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems]
    [IntoValTyped (GF := GF) GoInterface T] (l : Loc) (v : GoInterface) (ii : GoInterfaceOk),
  go.typeSetContains ii.ty T = true →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore ∗ l ↦ v }}
      (App (App (Val (@! Store)) (Val #(interface.mkOk (go.PointerType T) #l))) (Val #(interface.ok ii : GoInterface)))
    {{ RET #(); l ↦ (interface.ok ii : GoInterface) }})

end spec

end Perennial
