/-
`internal.reflectcore.PtrTok`'s spec.
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

/-- `PtrTok(t)` of a token (or any `any(p)`) of `*T`: the token of `*T`. -/
abbrev internal.reflectcore.PtrTok.spec : Prop :=
  ∀ (T : go.GoType) (v : val),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! PtrTok)) (Val #(interface.mkOk (go.PointerType T) v)))
    {{ RET #(go.tok (go.PointerType T)); True }}

end spec

end Perennial
