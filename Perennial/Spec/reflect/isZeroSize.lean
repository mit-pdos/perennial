/-
`reflect.isZeroSize`'s spec.
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- `isZeroSize(t)` for the token (or any pointer-any) of a type `T`: `zeroSizeN n T`, for any
`n` at which it is defined. -/
abbrev reflect.isZeroSize.spec : Prop :=
  ∀ (n : Nat) (T : go.GoType) (l : Loc) (b : Bool),
  reflect.zeroSizeN n T = some b →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! isZeroSize)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #b; True }}

end spec

end Perennial
