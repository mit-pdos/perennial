/-
`internal.reflectlite.unpackEface`'s spec.
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

/-- `unpackEface(i)` for `i` holding a value `x : V` of a non-interface type `t` of kind `k`, not of
the model `rtype`'s layout, whose `directIfaceN` is defined: the `Value` `valueOfRepr` describes
(direct, holding `i`; or indirect, holding `any(q)` for a new variable `q` holding `x`). -/
abbrev internal.reflectlite.unpackEface.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {t u : go.GoType} [t ↓u u]
    [IntoValTyped (GF := GF) V t] (k n : Nat) (b : Bool) (x : V),
  go.kindOf u = some k → go.isInterfaceType u = false →
  internal.reflectlite.rtypeLayoutU u = false → reflect.directIfaceN n t = some b →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! unpackEface)) (Val #(interface.mkOk t #x)))
    {{ (xv : Value), RET #xv; internal.reflectlite.valueOfRepr (GF := GF) xv t k x }}

end spec

end Perennial
