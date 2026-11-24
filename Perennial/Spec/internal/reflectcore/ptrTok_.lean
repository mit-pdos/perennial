/-
`internal.reflectcore.ptrTok`'s spec.
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

/-- `ptrTok[T](t)`: the token of `*T`, `any((**T)(nil))`. -/
abbrev internal.reflectcore.ptrTok.spec : Prop :=
  ∀ (T : go.GoType) (t : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val #(functions ptrTok [T])) (Val #t))
    {{ RET #(go.tok (go.PointerType T)); True }}

end spec

end Perennial
