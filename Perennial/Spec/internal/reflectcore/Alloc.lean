/-
`internal.reflectcore.Alloc`'s spec.
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

/-- `Alloc(t)` of a token (or any `any(p)`) of `*T`: a new variable `q` holding the zero `T`,
returned as `any(q)`. -/
abbrev internal.reflectcore.Alloc.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (v : val),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! Alloc)) (Val #(interface.mkOk (go.PointerType T) v)))
    {{ (q : Loc), RET #(interface.mkOk (go.PointerType T) #q); q ↦ zero_val V }}

end spec

end Perennial
