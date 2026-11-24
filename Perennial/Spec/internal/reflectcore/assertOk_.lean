/-
`internal.reflectcore.assertOk`'s spec.
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

/-- `assertOk[T](x)` for an interface type `T`: whether `x.(T)` succeeds (`x` non-nil and its
dynamic type in `T`'s type set). -/
abbrev internal.reflectcore.assertOk.spec : Prop :=
  ∀ {T : go.GoType} {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems] (x : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val #(functions assertOk [T])) (Val #x))
    {{ RET #(match x with
        | interface.nil => false
        | interface.ok ii => go.typeSetContains ii.ty T); True }}

end spec

end Perennial
