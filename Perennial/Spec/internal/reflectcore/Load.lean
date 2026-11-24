/-
`internal.reflectcore.Load`'s spec.
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

/-- `Load(p)` of `any(p)` for `p : *T`: `any(*p)`, which is `*p` itself for an interface type
`T`. -/
abbrev internal.reflectcore.Load.spec : Prop :=
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T Tu : go.GoType} [T ↓u Tu]
    [IntoValTyped (GF := GF) V T] (q : Loc) (dq : DFrac) (x : V),
  go.isInterfaceType Tu = false → go.isUntypedNil Tu = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore ∗ q ↦{dq} x }}
      (App (Val (@! Load)) (Val #(interface.mkOk (go.PointerType T) #q)))
    {{ RET #(interface.mkOk T #x); q ↦{dq} x }}) ∧
  (∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems] [IntoValTyped (GF := GF) V T]
    (q : Loc) (dq : DFrac) (x : V) (i : GoInterface),
  (#x : val) = #i →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore ∗ q ↦{dq} x }}
      (App (Val (@! Load)) (Val #(interface.mkOk (go.PointerType T) #q)))
    {{ RET #i; q ↦{dq} x }})

end spec

end Perennial
