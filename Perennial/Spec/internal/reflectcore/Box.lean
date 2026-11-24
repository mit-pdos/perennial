/-
`internal.reflectcore.Box`'s spec.
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

/-- `Box(x)` of a `T` (not an interface type) `x`: a new variable `q` holding `x`, returned
as `any(q)`. -/
abbrev internal.reflectcore.Box.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T Tu : go.GoType} [T ↓u Tu]
    [IntoValTyped (GF := GF) V T] (x : V),
  go.isInterfaceType Tu = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! Box)) (Val #(interface.mkOk T #x)))
    {{ (q : Loc), RET #(interface.mkOk (go.PointerType T) #q); q ↦ x }}

end spec

end Perennial
