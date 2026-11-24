/-
`reflect.Value.Interface`'s spec.
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

/-- `v.Interface()` of a direct `Value` of kind `Pointer` (22) holding `any(l)` for `l : *T`, not
read-only and not a method value: `any(l)`. -/
abbrev reflect.Value.Interface.spec : Prop :=
  ∀ (v : Value) (T : go.GoType) (l : Loc),
  v.typ_' = go.tok (go.PointerType T) → v.ptr' = interface.mkOk (go.PointerType T) #l →
  v.flag' &&& W64 31 = W64 22 → v.flag' &&& W64 736 = W64 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Interface")) (Val #()))
    {{ RET #(interface.mkOk (go.PointerType T) #l); True }}

end spec

end Perennial
