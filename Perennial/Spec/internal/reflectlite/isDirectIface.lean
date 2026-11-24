/-
`internal.reflectlite.isDirectIface`'s spec.
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

/-- `isDirectIface(t)` for the token (or any pointer-any) of a type `T`: `directIfaceN n T`, for
any `n` at which it is defined (for a kind other than `Array` and `Struct`, any `n > 0`:
`directIfaceN_of_kind`). -/
abbrev internal.reflectlite.isDirectIface.spec : Prop :=
  ∀ (n : Nat) (T : go.GoType) (l : Loc) (b : Bool),
  reflect.directIfaceN n T = some b →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! isDirectIface)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #b; True }}

end spec

end Perennial
