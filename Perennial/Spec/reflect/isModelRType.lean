/-
`reflect.isModelRType`'s spec.
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

/-- `isModelRType(t)` for the token (or any pointer-any) of a type `T` other than the model's
`rtype`: false. -/
abbrev reflect.isModelRType.spec : Prop :=
  ∀ (T : go.GoType) (l : Loc),
  T ≠ rtype.ty →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! isModelRType)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; True }}

end spec

end Perennial
